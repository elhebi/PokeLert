#!/usr/bin/env python3
"""PokeLert – Pokémon-TCG Vorbestell- und Release-Monitor.

Prüft Schweizer Shops, News und Communities, vergleicht Shop-Preise mit der
UVP und schickt Telegram-Alerts NUR für neue Vorbestellungen, wieder
verfügbare Vorbestellungen, Release-Ankündigungen und Release-Erinnerungen.
Außerdem wird eine Website (docs/index.html) erzeugt.

Nur Python-Standardbibliothek.

  python3 monitor.py                  # ein Durchlauf (mit Alerts)
  python3 monitor.py --dry-run --list # Probelauf, zeigt alle gefundenen Einträge
  python3 monitor.py --loop 10        # alle 10 Minuten wiederholen
  python3 monitor.py --test-telegram  # Testnachricht
"""
import argparse
import gzip
import html
import json
import os
import re
import sys
import time
import unicodedata
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
import hashlib
from datetime import date, datetime, timezone
from pathlib import Path

BASE = Path(__file__).parent
CONFIG_FILE = BASE / "config.json"
UVP_FILE = BASE / "uvp.json"
STATE_FILE = BASE / "state.json"
RELEASES_FILE = BASE / "releases.json"
SITE_FILE = BASE / "docs" / "index.html"
STATE_VERSION = 2
UA = "Mozilla/5.0 (compatible; PokeLert/2.0)"

PREORDER_RE = re.compile(r"vorbestell|pre-?order|pre order|précommande|precommande|vorverkauf", re.I)
SOLD_RE = re.compile(r"ausverkauft|nicht mehr bestellbar|out[- ]of[- ]stock|sold out|nicht verfügbar|"
                     r"nicht lieferbar|épuisé|currently unavailable", re.I)
DATE_RE = re.compile(r"\b(\d{1,2})\.(\d{1,2})\.(20\d{2})\b")
TAG_RE = re.compile(r"<[^>]+>")
GENERIC_LABEL = re.compile(r"^(add to cart|in den warenkorb|read more|mehr|details|zum produkt|"
                           r"select options|ansehen|view|more|weiter|jetzt kaufen|buy now)", re.I)


# ---------------------------------------------------------------- Helfer
def now_iso():
    return datetime.now(timezone.utc).astimezone().isoformat(timespec="seconds")


def log(*a):
    print(datetime.now().strftime("%H:%M:%S"), *a, flush=True)


def fetch(url, timeout=25, retries=2, data=None, headers=None):
    hdrs = {"User-Agent": UA, "Accept-Encoding": "gzip",
            "Accept-Language": "de-CH,de;q=0.9,en;q=0.7"}
    hdrs.update(headers or {})
    req = urllib.request.Request(url, data=data, headers=hdrs)
    for attempt in range(retries + 1):
        try:
            with urllib.request.urlopen(req, timeout=timeout) as r:
                data = r.read()
                if r.headers.get("Content-Encoding") == "gzip":
                    data = gzip.decompress(data)
                charset = r.headers.get_content_charset() or "utf-8"
            return data.decode(charset, errors="replace")
        except urllib.error.HTTPError as e:
            if e.code in (429, 500, 502, 503) and attempt < retries:
                time.sleep(5 * (attempt + 1))
                continue
            raise


def item_id(*parts):
    return hashlib.sha1("|".join(parts).encode()).hexdigest()[:16]


def load_json(path, default):
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (FileNotFoundError, json.JSONDecodeError):
        return default


def clean(s):
    return re.sub(r"\s+", " ", html.unescape(TAG_RE.sub(" ", s or ""))).strip()


def norm_url(u):
    u, _ = urllib.parse.urldefrag(u)
    base, _, query = u.partition("?")
    v = re.search(r"(?:^|&)variant=(\d+)", query)
    return base.rstrip("/") + (f"?variant={v.group(1)}" if v else "")


LANGS = [("DE", r"deutsch|german|\(de\)|-\s*de\b"), ("EN", r"englisch|english|\(en\)|-\s*en\b"),
         ("FR", r"franz[öo]sisch|french|français|\(fr\)|-\s*fr\b"),
         ("IT", r"italienisch|italian|italiano|\(it\)|-\s*it\b"),
         ("JP", r"japanisch|japanese|\bjpn\b|\(jp\)|-\s*jp\b"), ("CN", r"chinesisch|chinese|\bt?chn\b|\(cn\)|-\s*cn\b"),
         ("KR", r"koreanisch|korean|\(kr\)")]


def detect_language(text):
    t = (text or "").lower()
    for code, rx in LANGS:
        if re.search(rx, t):
            return code
    return ""


def norm(s):
    """Klein, ohne Akzente, nur Buchstaben/Ziffern, mit Leerzeichen am Rand (für Wortgrenzen)."""
    s = (s or "").lower().replace("ß", "ss")
    s = "".join(c for c in unicodedata.normalize("NFKD", s) if not unicodedata.combining(c))
    return " " + re.sub(r"[^a-z0-9]+", " ", s).strip() + " "


_ALIAS_CACHE = {}


def detect_set(title, sets):
    t = norm(title)
    best, best_len, fallback = "", 0, ""
    for st in sets:
        als = _ALIAS_CACHE.setdefault(st["id"], [norm(a) for a in st.get("aliases", [])])
        for a in als:
            if a in t:
                if st.get("fallback"):
                    fallback = fallback or st["id"]
                elif len(a) > best_len:
                    best, best_len = st["id"], len(a)
    return best or fallback


TYPES = [
    ("mini_tin_display", "Mini-Tin-Display", r"mini tin (display|set)|tin display"),
    ("display", "Booster Display", r"display|booster box"),
    ("etb", "Top Trainer Box / ETB", r"elite trainer|top trainer|\betb\b"),
    ("bundle", "Booster Bundle", r"bundle"),
    ("deck", "Decks & Kits", r"battle deck|build (and )?battle|kampfdeck|\bdeck\b|starter|battle academy"),
    ("blister", "Blister", r"blister|[23] pack|[23]er|checklane"),
    ("tin", "Tin / Mini Tin", r"\btin\b"),
    ("booster", "Einzelbooster", r"booster|\bpack\b"),
    ("kollektion", "Kollektionen & Boxen", r"kollektion|collection|premium|\bbox\b|\bset\b|binder|poster|sticker"),
]


def detect_type(title):
    t = norm(title)
    for tid, _label, rx in TYPES:
        if re.search(rx, t):
            return tid
    return "other"


def parse_num(s):
    s = s.strip(".,").replace("'", "").replace("’", "").replace(" ", "")
    if "," in s and "." in s:
        s = s.replace(",", "")
    elif "," in s:
        s = s.replace(",", ".")
    try:
        return float(s)
    except ValueError:
        return None


def iso_date(text):
    m = DATE_RE.search(text or "")
    if not m:
        return None
    try:
        return date(int(m.group(3)), int(m.group(2)), int(m.group(1))).isoformat()
    except ValueError:
        return None


def fmt_date(iso):
    try:
        return datetime.strptime(iso, "%Y-%m-%d").strftime("%d.%m.%Y")
    except (TypeError, ValueError):
        return ""


def is_pokemon(text):
    return bool(re.search(r"pok[eé]mon|pikachu|glurak|charizard|mega[- ]entwicklung|mega evolution", text, re.I))


# ---------------------------------------------------------------- News-Bewertung
def news_score(text, cfg, extra_ignore=()):
    t = text.lower()
    for kw in list(cfg.get("ignore", [])) + list(extra_ignore):
        if kw.lower() in t:
            return -1, []
    pts, hits = 0, []
    for kw, w in cfg["release_keywords"].items():
        if kw.lower() in t:
            pts += w
            hits.append(kw)
    return pts, hits


# ---------------------------------------------------------------- Quellen: Feeds
def parse_feed(xml_text, source):
    items = []
    root = ET.fromstring(xml_text)
    ns = {"a": "http://www.w3.org/2005/Atom"}
    for e in root.iter("item"):
        items.append({"title": (e.findtext("title") or "").strip(),
                      "url": (e.findtext("link") or "").strip(),
                      "summary": e.findtext("description") or ""})
    for e in root.findall("a:entry", ns):
        link = e.find("a:link", ns)
        items.append({"title": (e.findtext("a:title", "", ns) or "").strip(),
                      "url": link.get("href", "") if link is not None else "",
                      "summary": e.findtext("a:summary", "", ns) or ""})
    for it in items:
        it["source"] = source["name"]
        it["kind"] = "news"
        it["summary"] = clean(it["summary"])[:300]
    return items


def parse_telegram(html_text, source):
    items = []
    for block in html_text.split("tgme_widget_message_wrap")[1:]:
        m_link = re.search(r'tgme_widget_message_date"[^>]*href="([^"]+)"', block)
        m_text = re.search(r'tgme_widget_message_text[^>]*>(.*?)</div>', block, re.S)
        if not (m_link and m_text):
            continue
        text = clean(re.sub(r"<br\s*/?>", " ", m_text.group(1)))
        items.append({"title": text[:140], "url": m_link.group(1), "summary": text[:300],
                      "source": source["name"], "kind": "social"})
    return items


def social_url(src):
    t, n = src["type"], src.get("handle", "")
    if t == "reddit":
        return f"https://www.reddit.com/r/{n}/new/.rss"
    if t == "youtube":
        return f"https://www.youtube.com/feeds/videos.xml?channel_id={n}"
    if t == "bluesky":
        return f"https://bsky.app/profile/{n}/rss"
    if t == "mastodon":
        return f"https://{n}.rss"
    return src["url"]


# ---------------------------------------------------------------- Quellen: Shops
def shop_item(src, title, url, price, currency, available, preorder, release):
    today = date.today().isoformat()
    if release and release > today:
        preorder = True
    return {"title": title.strip(), "url": url, "summary": "", "source": src["name"],
            "kind": "shop", "price": price, "currency": currency, "available": available,
            "preorder": bool(preorder), "release": release}


def parse_shopify(src):
    base = src["url"].rstrip("/")
    path = f"/collections/{src['collection']}" if src.get("collection") else ""
    items = []
    for page in range(1, src.get("pages", 3) + 1):
        data = json.loads(fetch(f"{base}{path}/products.json?limit=250&page={page}"))
        prods = data.get("products", [])
        if not prods:
            break
        for p in prods:
            variants = p.get("variants") or []
            tags = p.get("tags", "")
            tags = " ".join(tags) if isinstance(tags, list) else str(tags)
            title = p.get("title", "")
            blob = f"{title} {tags} {p.get('product_type', '')}"
            pre = src.get("preorder_page") or bool(PREORDER_RE.search(blob))
            url = f"{base}/products/{p.get('handle', '')}"
            lang_vars = [(detect_language(v.get("title", "")), v) for v in variants if len(variants) > 1]
            if lang_vars and all(l for l, _ in lang_vars) and len({l for l, _ in lang_vars}) == len(lang_vars):
                # Ein Eintrag pro Sprachvariante (Preis und Lager können je Sprache verschieden sein)
                for lang, v in lang_vars:
                    price = parse_num(str(v.get("price", "")))
                    it = shop_item(src, f"{title} ({lang})", f"{url}?variant={v.get('id')}",
                                   price or None, src.get("currency", "CHF"),
                                   bool(v.get("available")), pre, None)
                    it["language"] = lang
                    items.append(it)
                continue
            prices = [parse_num(str(v.get("price", ""))) for v in variants]
            prices = [x for x in prices if x]
            it = shop_item(src, title, url, min(prices) if prices else None, src.get("currency", "CHF"),
                           any(v.get("available") for v in variants) if variants else None, pre, None)
            items.append(it)
        if len(prods) < 250:
            break
    return items


def parse_wog(src):
    """World of Games lädt seine Listen per Schnittstelle nach (JSON)."""
    base = src.get("url", "https://www.wog.ch").rstrip("/")
    items, page, total = [], 1, None
    while page <= 5:
        body = urllib.parse.urlencode({
            "listType": "releases", "maxRows": 300, "page": page, "view": "tile",
            "platform": src.get("platform", "Trading-Cards")}).encode()
        data = json.loads(fetch(f"{base}/index.cfm/ajax.productList", data=body, headers={
            "X-Requested-With": "XMLHttpRequest", "Origin": base,
            "Referer": f"{base}/de/index.cfm/releases/platform/{src.get('platform', 'Trading-Cards')}"}))
        prods = data.get("products", [])
        total = data.get("totalRows", len(prods))
        for p in prods:
            title = p.get("fullTitle") or p.get("title") or ""
            price = p.get("unitPrice")
            price = float(price) if price not in (None, "", 0, "0") else None
            sold = p.get("delivery") == 4 or SOLD_RE.search(str(p.get("deliveryText", ""))) or \
                "nicht mehr lieferbar" in str(p.get("deliveryText", "")).lower()
            items.append(shop_item(src, title, p.get("linkTo", ""), price, "CHF", not sold, True,
                                   iso_date(p.get("releaseDateOnly") or p.get("releaseDate") or "")))
        if len(items) >= total or not prods:
            break
        page += 1
    return items


def parse_shop_html(text, src, page_url):
    """Findet Produkte auf einer Listenseite (WooCommerce, PrestaShop, Shopware …)."""
    must = [m.lower() for m in src.get("link_must_contain", [])]
    must_not = [m.lower() for m in src.get("link_must_not_contain", ["add-to-cart", "javascript:"])]
    # Unsichtbares entfernen, damit nur sichtbarer Text und Preise übrig bleiben
    text = re.sub(r"<(script|style|noscript|svg)\b.*?</\1>|<!--.*?-->", " ", text, flags=re.I | re.S)
    foot = re.search(r"<footer\b", text, re.I)
    if foot:
        text = text[:foot.start()]
    anchors = []
    for m in re.finditer(r'<a\s[^>]*?href=["\']([^"\']+)["\'][^>]*>(.*?)</a>', text, re.I | re.S):
        full = norm_url(urllib.parse.urljoin(page_url, html.unescape(m.group(1))))
        low = full.lower()
        if full == norm_url(page_url) or not full.startswith("http"):
            continue
        if any(x not in low for x in must) or any(x in low for x in must_not):
            continue
        anchors.append((m.start(), full, clean(m.group(2))))
    # Jede Fundstelle eines Produkts gilt bis zum nächsten anderen Produkt; die
    # Bereiche aller Fundstellen eines Produkts werden zusammengefasst.
    windows, labels_by = {}, {}
    for idx, (pos, full, label) in enumerate(anchors):
        end = pos + 12000
        for pos2, full2, _ in anchors[idx + 1:]:
            if full2 != full:
                end = min(end, pos2)
                break
        windows.setdefault(full, []).append(text[pos:end])
        labels_by.setdefault(full, []).append(label)
    items = []
    for full, wins in windows.items():
        window = " ".join(dict.fromkeys(wins))
        wtext = clean(window)
        labels = labels_by[full]
        labels += [clean(a) for a in re.findall(r'alt=["\']([^"\']+)["\']', window)]
        labels = [x for x in labels if len(x) >= 8 and not GENERIC_LABEL.match(x)
                  and not re.fullmatch(r"[\sCHFr.\d'’,–-]+", x)]
        if not labels:
            continue
        title = max(labels, key=len)[:200]
        nums = re.findall(r"(?:CHF|Fr\.)\s*([0-9][0-9'’.,]*)", wtext, re.I) or \
            re.findall(r"([0-9][0-9'’.,]*)\s*(?:CHF|Fr\.)", wtext, re.I)
        prices = [x for x in (parse_num(n) for n in nums) if x]
        items.append(shop_item(
            src, title, full, min(prices) if prices else None, "CHF",
            not SOLD_RE.search(wtext),
            src.get("preorder_page") or bool(PREORDER_RE.search(title + " " + wtext)),
            iso_date(wtext)))
    return items


# ---------------------------------------------------------------- Preisbewertung
def rate(it, cfg, uvp, cur=False):
    """Ergänzt UVP, Richtpreis und Bewertung (fair / teuer / reseller)."""
    it.update(uvp_eur=None, uvp_chf=None, uvp_is_ref=False, uvp_name="", rating="", price_chf=None, ratio=None)
    foreign = it.get("country", "CH") != "CH"
    title = it["title"].lower()
    prod = None
    for p in uvp["products"]:
        if any(m in title for m in p["match"]) and not any(x in title for x in p.get("exclude", [])):
            prod = p
            break
    if not prod:
        return
    if not (cur or it.get("preorder")):
        return
    rate_eur = uvp["eur_chf"]
    it["uvp_eur"], it["uvp_name"] = prod["uvp_eur"], prod["name"]
    if it.get("price") is None:
        return
    price_chf = it["price"] if it["currency"] == "CHF" else it["price"] * rate_eur
    it["price_chf"] = round(price_chf, 2)
    uvp_chf = prod.get("chf_ref") or prod["uvp_eur"] * rate_eur
    it["uvp_chf"] = round(uvp_chf, 2)
    it["uvp_is_ref"] = bool(prod.get("chf_ref"))
    ratio = price_chf / uvp_chf
    it["ratio"] = round(ratio, 2)
    if foreign:
        return  # Ausland: Preis nur anzeigen (Zoll/MwSt/Versand nicht vergleichbar), keine Bewertung
    th = uvp["thresholds"]
    it["rating"] = "fair" if ratio <= th["fair"] else "teuer" if ratio <= th["teuer"] else "reseller"


def shop_relevant(it, cfg):
    t = (it["title"] + " " + it["url"]).lower()
    if not it.get("all_pokemon") and not is_pokemon(t):
        return False
    if any(x in t for x in cfg.get("shop_exclude", [])):
        return False
    return any(k in t for k in cfg.get("product_keywords", []))


# ---------------------------------------------------------------- Einsammeln
def collect(cfg):
    out, status = [], {}
    first = True
    for src in cfg["sources"]:
        if src.get("enabled") is False:
            continue
        if not first:
            time.sleep(src.get("pause", 2))
        first = False
        name, t = src["name"], src["type"]
        try:
            if t == "telegram":
                s2 = dict(src, url=f"https://t.me/s/{src['handle']}")
                items = parse_telegram(fetch(s2["url"]), s2)
            elif t == "shopify":
                items = parse_shopify(src)
            elif t == "wog":
                items = parse_wog(src)
            elif t == "shop":
                items = []
                for i, url in enumerate(src.get("urls") or [src["url"]]):
                    try:
                        items += parse_shop_html(fetch(url), src, url)
                    except Exception as ex:
                        if i == 0:
                            raise
                        log(f"  (Zusatzseite übersprungen: {url}: {ex})")
            else:  # rss, reddit, youtube, bluesky, mastodon
                items = parse_feed(fetch(social_url(src)), src)
                if t != "rss":
                    for it in items:
                        it["kind"] = "social"
            for it in items:
                it["all_pokemon"] = bool(src.get("all_pokemon"))
                it["country"] = src.get("country", "CH")
                if it["kind"] == "shop" and not it.get("language"):
                    it["language"] = detect_language(it["title"])
                it["extra_ignore"] = src.get("ignore", [])
            log(f"{name}: {len(items)} Einträge")
            out.extend(items)
            status[name] = {"count": len(items), "error": "", "time": now_iso()}
        except Exception as ex:
            log(f"FEHLER {name}: {ex}")
            status[name] = {"count": 0, "error": str(ex)[:120], "time": now_iso()}
    return out, status


# ---------------------------------------------------------------- Telegram
def send_telegram(text):
    token = os.environ.get("TELEGRAM_BOT_TOKEN")
    chat = os.environ.get("TELEGRAM_CHAT_ID")
    if not token or not chat:
        log("Telegram nicht konfiguriert (TELEGRAM_BOT_TOKEN / TELEGRAM_CHAT_ID fehlen)")
        return False
    ok = False
    for chat_id in [c.strip() for c in re.split(r"[,;\s]+", chat) if c.strip()]:  # mehrere Empfänger möglich
        data = urllib.parse.urlencode({"chat_id": chat_id, "text": text, "parse_mode": "HTML",
                                       "disable_web_page_preview": "false"}).encode()
        try:
            urllib.request.urlopen(f"https://api.telegram.org/bot{token}/sendMessage", data, timeout=20)
            ok = True
        except Exception as ex:
            log(f"Telegram-Fehler ({chat_id}): {ex}")
    return ok


EVENT_HEAD = {"new_preorder": "🆕 Neue Vorbestellung", "restock": "🔁 Wieder verfügbar",
              "release_news": "📣 Release-News", "reminder": "📅 Erinnerung"}


def format_alert(rec, eur_chf):
    e = html.escape
    lines = [f"{EVENT_HEAD[rec['event']]}", f"<b>{e(rec['title'])}</b>"]
    if rec["kind"] == "shop":
        lines.append(f"🏪 {e(rec['source'])}" + ("  🌍 Ausland – Zoll/MwSt prüfen" if rec.get("country", "CH") != "CH" else ""))
        if rec.get("price") is not None:
            r = {"fair": "✅ fairer Preis", "teuer": "⚠️ über UVP", "reseller": "🚫 Reseller-Preis"}.get(rec.get("rating"), "")
            lines.append(f"💰 {rec['currency']} {rec['price']:.2f} {r}".strip())
        if rec.get("uvp_eur"):
            ref = "CH-Richtpreis" if rec.get("uvp_is_ref") else "umgerechnet"
            lines.append(f"UVP: € {rec['uvp_eur']:.2f} · {ref} CHF {rec.get('uvp_chf') or rec['uvp_eur'] * eur_chf:.2f}")
        if rec.get("release"):
            lines.append(f"📅 Release: {fmt_date(rec['release'])}")
    else:
        lines.append(f"Quelle: {e(rec['source'])}")
    lines.append(rec["url"])
    return "\n".join(lines)


# ---------------------------------------------------------------- Website
TEMPLATE_FILE = BASE / "site_template.html"


def money(cur, v):
    return f"{cur} {v:.2f}" if v is not None else "–"


def render_site(state, releases, eur_chf, th, cfg=None):
    cfg = cfg or load_json(CONFIG_FILE, {})
    sets = cfg.get("sets", [])
    set_info = {st["id"]: {"n": st["name"], "cur": bool(st.get("current")), "al": st.get("aliases", [])[:6]} for st in sets}
    today = date.today()
    items = []
    for i in state["items"].values():
        if i["kind"] != "shop":
            continue
        rel = i.get("release")
        pre = bool(i.get("preorder")) or bool(rel and rel >= today.isoformat())
        items.append({
            "t": i["title"], "u": i["url"], "s": i["source"], "c": i.get("country", "CH"),
            "l": i.get("language", ""), "p": i.get("price"), "cur": i.get("currency", "CHF"),
            "pc": i.get("price_chf"), "a": 1 if i.get("available") else 0 if i.get("available") is False else -1,
            "pre": 1 if pre else 0, "r": rel, "rt": i.get("rating", ""), "ra": i.get("ratio"),
            "ue": i.get("uvp_eur"), "uc": i.get("uvp_chf"), "ur": 1 if i.get("uvp_is_ref") else 0,
            "ty": detect_type(i["title"]), "st": detect_set(i["title"], sets), "fs": i["first_seen"][:16],
            "n": 1 if i.get("alerted") and i["first_seen"][:10] >= today.isoformat() else 0})
    news = sorted((i for i in state["items"].values() if i["kind"] != "shop"),
                  key=lambda i: i["first_seen"], reverse=True)[:40]
    news = [{"t": n["title"], "u": n["url"], "s": n["source"], "k": n["kind"], "fs": n["first_seen"]} for n in news]
    status = state.get("sources", {})
    shops = []
    for x in cfg.get("sources", []):
        if x.get("type") in ("shop", "shopify", "wog") and x.get("enabled") is not False:
            stt = status.get(x["name"], {})
            shops.append({"n": x["name"].split(" (")[0], "c": x.get("country", "CH"), "u": x.get("url") or (x.get("urls") or [""])[0],
                          "m": "automatisch überwacht" if not stt.get("error") else "Fehler beim letzten Lauf",
                          "cnt": stt.get("count"), "note": stt.get("error", "")})
    for d in cfg.get("directory", []):
        shops.append({"n": d["name"], "c": d.get("country", "CH"), "u": d["url"], "m": "manuell prüfen",
                      "cnt": None, "note": d.get("note", "")})
    data = {"items": items, "news": news, "shops": shops, "sets": set_info,
            "types": dict([(tid, label) for tid, label, _ in TYPES] + [("other", "Sonstiges")]),
            "cal": [{"date": r["date"], "name": r["name"], "note": r.get("note", ""), "url": r.get("url", "")}
                    for r in sorted(releases, key=lambda r: r["date"])],
            "meta": {"generated": state.get("last_run") or now_iso(), "today": today.isoformat(),
                     "eur_chf": eur_chf, "th": th, "repo": cfg.get("repo", "")}}
    blob = json.dumps(data, ensure_ascii=False, separators=(",", ":")).replace("</", "<\\/")
    return TEMPLATE_FILE.read_text(encoding="utf-8").replace("/*DATA*/", blob)


# ---------------------------------------------------------------- Hauptlogik
def run(cfg, dry=False, alert_initial=False, show=False):
    uvp = load_json(UVP_FILE, {"products": [], "eur_chf": 0.93, "thresholds": {"fair": 1.1, "teuer": 1.3}})
    state = load_json(STATE_FILE, {})
    old_sig, old_written = state.get("sig"), state.get("written_at", 0)
    if state.get("version") != STATE_VERSION:
        old_sig = None
        state = {"version": STATE_VERSION, "items": {}, "reminders": [], "sources": {}, "last_run": ""}
    first_run = not state["items"]
    releases = load_json(RELEASES_FILE, [])
    eur_chf = uvp["eur_chf"]
    alerts = []

    collected, status = collect(cfg)
    state["sources"] = status
    ok_ratings = set(cfg.get("alert_ratings", ["fair", "teuer", ""]))

    for it in collected:
        if not it.get("url") or not it.get("title"):
            continue
        iid = item_id(norm_url(it["url"]))
        old = state["items"].get(iid)
        event = None
        if it["kind"] == "shop":
            if not shop_relevant(it, cfg):
                continue
            tl = it["title"].lower()
            sid = detect_set(it["title"], cfg.get("sets", []))
            set_cur = any(st["id"] == sid and st.get("current") for st in cfg.get("sets", []))
            cur = bool(it["preorder"] or set_cur or any(x in tl for x in cfg.get("current_sets", [])))
            rate(it, cfg, uvp, cur)
            if show:
                print(f"  [{it['source']}] {it['title'][:80]} | {money(it['currency'], it['price'])} | "
                      f"{'bestellbar' if it['available'] else 'ausverkauft'} | "
                      f"{'VORBESTELLUNG' if it['preorder'] else ''} {it.get('release') or ''} | {it['rating'] or '-'}")
            if old is None and it["preorder"] and it["available"] is not False:
                event = "new_preorder"
            elif old is not None and it["available"] and old.get("available") is False and cur:
                event = "restock"
            if event and it["rating"] not in ok_ratings:
                event = None  # Reseller-Preis: nur auf der Website, kein Alert
            if event and it.get("language") and it["language"] not in cfg.get("alert_languages", ["DE", "EN"]):
                event = None  # andere Sprache (z. B. FR/IT/JP): nur auf der Website
        else:
            if show:
                print(f"  [{it['source']}] {it['title'][:90]}")
            if old is not None:
                continue
            pts, hits = news_score(f"{it['title']} {it['summary']}", cfg, it.get("extra_ignore", []))
            if pts < 0:
                continue
            if pts >= cfg["alert_threshold"] and (it.get("all_pokemon") or is_pokemon(it["title"] + it["summary"])):
                event = "release_news"
        rec = dict(old or {})
        keep = ["title", "url", "source", "kind", "price", "currency", "available", "preorder",
                "release", "country", "language", "uvp_eur", "uvp_chf", "uvp_is_ref", "uvp_name", "rating", "price_chf", "ratio"]
        rec.update({k: it.get(k) for k in keep if k in it})
        rec.setdefault("first_seen", now_iso())
        rec.update(id=iid, last_seen=now_iso(), summary=(it.get("summary") or "")[:200] if it["kind"] != "shop" else "")
        rec["alerted"] = bool(rec.get("alerted") or event)
        state["items"][iid] = rec
        if event:
            alerts.append(dict(rec, event=event))

    # Release-Erinnerungen
    for r in releases:
        try:
            days = (datetime.strptime(r["date"], "%Y-%m-%d").date() - date.today()).days
        except (KeyError, ValueError):
            continue
        if days in cfg.get("reminder_days", [7, 1, 0]):
            key = f"{r['name']}|{r['date']}|{days}"
            if key not in state["reminders"]:
                state["reminders"].append(key)
                when = "heute" if days == 0 else "morgen" if days == 1 else f"in {days} Tagen"
                alerts.append({"event": "reminder", "kind": "reminder", "source": "Kalender",
                               "title": f"{r['name']} erscheint {when} ({fmt_date(r['date'])})",
                               "url": r.get("url", ""), "rating": "fair", "price": None})

    if first_run and not alert_initial:
        log(f"Erster Lauf: {len(alerts)} bestehende Treffer werden still gespeichert.")
        alerts = [a for a in alerts if a["event"] == "reminder"]

    prio = {"restock": 0, "new_preorder": 1, "reminder": 2, "release_news": 3}
    alerts.sort(key=lambda a: (prio[a["event"]], {"fair": 0, "": 1, "teuer": 2}.get(a.get("rating", ""), 1)))
    for a in alerts[: cfg.get("max_alerts_per_run", 10)]:
        log("ALERT:", a["event"], "-", a["title"])
        if not dry:
            msg = format_alert(a, eur_chf) if a["event"] != "reminder" else f"📅 Erinnerung\n<b>{html.escape(a['title'])}</b>\n{a['url']}"
            send_telegram(msg)

    state["last_run"] = now_iso()
    # Aufräumen: verschwundene Shop-Einträge nach 21 Tagen, News auf 300 begrenzen
    cutoff = time.time() - 21 * 86400
    for k in [k for k, v in state["items"].items() if v["kind"] == "shop"
              and datetime.fromisoformat(v["last_seen"]).timestamp() < cutoff]:
        del state["items"][k]
    news = sorted((v for v in state["items"].values() if v["kind"] != "shop"), key=lambda v: v["first_seen"])
    for v in news[:-300]:
        del state["items"][v["id"]]
    state["reminders"] = state["reminders"][-200:]

    sig = hashlib.sha1(json.dumps(
        [{k: {a: b for a, b in v.items() if a != "last_seen"} for k, v in state["items"].items()},
         state["reminders"], {k: [v["count"], v["error"]] for k, v in state["sources"].items()}],
        ensure_ascii=False, sort_keys=True).encode()).hexdigest()
    changed = sig != old_sig or time.time() - old_written > 6 * 3600
    if not dry and not changed:
        log("Keine Änderungen – nichts zu speichern.")
    if not dry and changed:
        state["sig"], state["written_at"] = sig, time.time()
        STATE_FILE.write_text(json.dumps(state, ensure_ascii=False, separators=(",", ":")), encoding="utf-8")
        SITE_FILE.parent.mkdir(exist_ok=True)
        SITE_FILE.write_text(render_site(state, releases, eur_chf, uvp['thresholds'], cfg), encoding="utf-8")
        log(f"Website aktualisiert: {SITE_FILE}")
    return len(alerts)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--loop", type=int, metavar="MIN")
    ap.add_argument("--alert-initial", action="store_true")
    ap.add_argument("--test-telegram", action="store_true")
    ap.add_argument("--list", action="store_true", help="alle gefundenen Einträge anzeigen")
    a = ap.parse_args()
    cfg = load_json(CONFIG_FILE, None)
    if cfg is None:
        sys.exit("config.json fehlt oder ist ungültig")
    if a.test_telegram:
        sys.exit(0 if send_telegram("✅ PokeLert: Telegram funktioniert.") else 1)
    while True:
        run(cfg, dry=a.dry_run, alert_initial=a.alert_initial, show=a.list)
        if not a.loop:
            break
        time.sleep(a.loop * 60)


if __name__ == "__main__":
    main()
