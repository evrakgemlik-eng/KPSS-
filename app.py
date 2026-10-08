# ============================================================
# KPSS İLAN AVCISI
# Kişisel Kamu Personel İlan Tarama ve Uygunluk Sistemi
#
# Çalıştırma:
#     streamlit run app.py
#
# GitHub / Streamlit için:
#     app.py
#     requirements.txt
#
# Sistem:
# - Kariyer Kapısı
# - İlan.gov.tr
# - Resmî Gazete
# - ÖSYM
# - İŞKUR (opsiyonel)
# - Kullanıcının eklediği kamu kurumları
# - HTML + PDF ilan taraması
# - KPSS puanı
# - KPSS puan türü
# - Mezuniyet
# - Bölüm
# - Nitelik kodu
# - Bilgisayar sertifikası
# - Son başvuru tarihi
# - Otomatik uygunluk değerlendirmesi
# ============================================================

import re
import time
import heapq
import hashlib
import urllib.robotparser
from io import BytesIO
from dataclasses import dataclass
from datetime import datetime
from urllib.parse import urljoin, urlparse, urlunparse

import requests
import pandas as pd
import streamlit as st
from bs4 import BeautifulSoup

try:
    from pypdf import PdfReader
    PDF_SUPPORT = True
except Exception:
    PDF_SUPPORT = False


# ============================================================
# SAYFA AYARLARI
# ============================================================

st.set_page_config(
    page_title="KPSS İlan Avcısı",
    page_icon="🎯",
    layout="wide",
    initial_sidebar_state="expanded"
)


# ============================================================
# SABİTLER
# ============================================================

USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
    "AppleWebKit/537.36 (KHTML, like Gecko) "
    "Chrome/128.0 Safari/537.36 "
    "KPSS-Ilan-Avcisi/1.0"
)

REQUEST_TIMEOUT = 20
MAX_DOWNLOAD_MB = 12
DEFAULT_DELAY = 0.5

RECRUITMENT_KEYWORDS = [
    "personel alımı",
    "personel alimi",
    "personel alımı ilanı",
    "personel alimi ilani",
    "sözleşmeli personel",
    "sozlesmeli personel",
    "memur alımı",
    "memur alimi",
    "kamu personel",
    "büro personeli",
    "buro personeli",
    "uzman yardımcısı",
    "uzman yardimcisi",
    "uzman yardımcılığı",
    "uzman yardimciligi",
    "denetçi yardımcısı",
    "denetci yardimcisi",
    "müfettiş yardımcısı",
    "mufettis yardimcisi",
    "veri hazırlama",
    "veri hazirlama",
    "bilgisayar işletmeni",
    "bilgisayar isletmeni",
    "kariyer kapısı",
    "kariyer kapisi",
    "başvuru",
    "basvuru",
    "kpss",
    "ilan",
    "alım",
    "alim",
    "sözlü sınav",
    "sozlu sinav",
    "yazılı sınav",
    "yazili sinav"
]

TARGET_JOB_KEYWORDS = [
    "memur",
    "büro personeli",
    "buro personeli",
    "büro görevlisi",
    "buro gorevlisi",
    "veri hazırlama",
    "veri hazirlama",
    "veri hazırlama ve kontrol işletmeni",
    "veri hazirlama ve kontrol isletmeni",
    "bilgisayar işletmeni",
    "bilgisayar isletmeni",
    "uzman yardımcısı",
    "uzman yardimcisi",
    "personel",
    "memur yardımcısı",
    "memur yardimcisi"
]

DEPARTMENT_KEYWORDS = [
    "siyaset bilimi ve kamu yönetimi",
    "siyaset bilimi ve kamu yonetimi",
    "siyaset bilimi-kamu yönetimi",
    "siyaset bilimi",
    "kamu yönetimi",
    "kamu yonetimi",
    "political science and public administration",
    "public administration",
    "kamu yönetimi bölümü",
    "kamu yonetimi bolumu",
    "iibf",
    "iktisadi ve idari bilimler fakültesi",
    "iktisadi ve idari bilimler fakultesi"
]

GENERAL_LICENSE_WORDS = [
    "lisans mezunu",
    "lisans mezunlarından",
    "lisans programlarının",
    "herhangi bir lisans",
    "dört yıllık fakülte",
    "dort yillik fakult",
    "yükseköğretim kurumlarının lisans",
    "yuksekogretim kurumlarinin lisans"
]

CERTIFICATE_KEYWORDS = [
    "6225",
    "bilgisayar işletmeni sertifikası",
    "bilgisayar isletmeni sertifikasi",
    "bilgisayar programcısı sertifikası",
    "bilgisayar programcisi sertifikasi",
    "meb onaylı bilgisayar",
    "meb onayli bilgisayar",
    "bilgisayar sertifikası",
    "bilgisayar sertifikasi",
    "bilgisayar belgesi"
]

KPSSTYPES = ["P3", "P1", "P2", "P93", "P94", "P121", "P48"]


# ============================================================
# KAYNAK TANIMI
# ============================================================

@dataclass
class Source:
    name: str
    url: str
    enabled: bool = True
    max_pages: int = 30


DEFAULT_SOURCES = [
    Source(
        "Kariyer Kapısı",
        "https://kariyerkapisi.gov.tr/isealim",
        True,
        50
    ),
    Source(
        "İlan.gov.tr",
        "https://www.ilan.gov.tr/ilan/tum-ilanlar",
        True,
        40
    ),
    Source(
        "Resmî Gazete",
        "https://resmigazete.gov.tr/",
        True,
        30
    ),
    Source(
        "ÖSYM",
        "https://www.osym.gov.tr/Duyurular/Index",
        True,
        30
    ),
    Source(
        "İŞKUR Açık İş",
        "https://acikisharita.iskur.gov.tr/",
        False,
        25
    )
]


# ============================================================
# SESSION
# ============================================================

session = requests.Session()
session.headers.update({
    "User-Agent": USER_AGENT,
    "Accept-Language": "tr-TR,tr;q=0.9,en-US;q=0.8,en;q=0.7"
})

robots_cache = {}


# ============================================================
# YARDIMCI FONKSİYONLAR
# ============================================================

def normalize_text(text):
    if not text:
        return ""

    text = str(text)
    text = text.replace("\xa0", " ")

    replacements = {
        "İ": "i",
        "I": "ı",
        "Ş": "ş",
        "Ğ": "ğ",
        "Ü": "ü",
        "Ö": "ö",
        "Ç": "ç"
    }

    for a, b in replacements.items():
        text = text.replace(a, b)

    text = re.sub(r"\s+", " ", text)
    return text.strip().lower()


def clean_display_text(text):
    if not text:
        return ""

    text = re.sub(r"\s+", " ", str(text))
    return text.strip()


def canonical_url(url):
    """
    Aynı sayfanın farklı fragment/query varyasyonlarını mümkün
    olduğunca tekilleştirir.
    """
    try:
        p = urlparse(url)

        if p.scheme not in ("http", "https"):
            return None

        clean_path = p.path or "/"

        # Fragment gereksiz.
        return urlunparse((
            p.scheme.lower(),
            p.netloc.lower(),
            clean_path,
            "",
            p.query,
            ""
        ))
    except Exception:
        return None


def hostname(url):
    try:
        host = urlparse(url).hostname
        if not host:
            return ""
        host = host.lower()
        if host.startswith("www."):
            host = host[4:]
        return host
    except Exception:
        return ""


def same_domain(url_a, url_b):
    return hostname(url_a) == hostname(url_b)


def is_pdf_url(url):
    return url.lower().split("?")[0].endswith(".pdf")


def allowed_by_robots(url):
    """
    robots.txt kurallarına mümkün olduğunca uyar.
    Robots okunamazsa taramayı tamamen durdurmak yerine
    güvenli tarafta kalmak için False dönülür.
    """

    host = hostname(url)

    if host in robots_cache:
        rp = robots_cache[host]
    else:
        try:
            robots_url = f"https://{host}/robots.txt"

            rp = urllib.robotparser.RobotFileParser()
            rp.set_url(robots_url)
            rp.read()

            robots_cache[host] = rp
        except Exception:
            # Robots okunamazsa erişimi tamamen kesmiyoruz.
            # Ancak çok agresif tarama yapılmayacak.
            return True

    try:
        return rp.can_fetch(USER_AGENT, url)
    except Exception:
        return True


def stable_id(url, title=""):
    raw = f"{url}|{title}".encode("utf-8", errors="ignore")
    return hashlib.sha256(raw).hexdigest()[:16]


def contains_any(text, keywords):
    t = normalize_text(text)

    for keyword in keywords:
        if normalize_text(keyword) in t:
            return True

    return False


def keyword_hits(text, keywords):
    t = normalize_text(text)
    hits = []

    for keyword in keywords:
        normalized = normalize_text(keyword)

        if normalized in t:
            hits.append(keyword)

    return list(dict.fromkeys(hits))


# ============================================================
# PDF ÇIKARMA
# ============================================================

def extract_pdf_text(data):
    if not PDF_SUPPORT:
        return ""

    try:
        reader = PdfReader(BytesIO(data))

        pages = []

        for page in reader.pages:
            try:
                text = page.extract_text() or ""
                pages.append(text)
            except Exception:
                continue

        return clean_display_text(" ".join(pages))

    except Exception:
        return ""


# ============================================================
# HTTP İNDİRME
# ============================================================

def fetch_url(url):
    """
    HTML veya PDF indirir.
    """

    if not allowed_by_robots(url):
        return None, None, "robots.txt izin vermiyor"

    try:
        response = session.get(
            url,
            timeout=REQUEST_TIMEOUT,
            allow_redirects=True,
            stream=True
        )

        if response.status_code != 200:
            return None, None, f"HTTP {response.status_code}"

        content_length = response.headers.get("Content-Length")

        if content_length:
            try:
                if int(content_length) > MAX_DOWNLOAD_MB * 1024 * 1024:
                    return None, None, "Dosya çok büyük"
            except Exception:
                pass

        content = response.content

        if len(content) > MAX_DOWNLOAD_MB * 1024 * 1024:
            return None, None, "Dosya çok büyük"

        content_type = (
            response.headers.get("Content-Type", "")
            .lower()
        )

        if (
            "application/pdf" in content_type
            or is_pdf_url(response.url)
            or is_pdf_url(url)
        ):
            return content, "pdf", None

        return content, "html", None

    except requests.exceptions.Timeout:
        return None, None, "Zaman aşımı"

    except requests.exceptions.RequestException as e:
        return None, None, str(e)

    except Exception as e:
        return None, None, str(e)


# ============================================================
# İLAN ALANLARINI ÇIKARMA
# ============================================================

def extract_title(soup, url):
    title = ""

    if soup.title:
        title = soup.title.get_text(" ", strip=True)

    if not title:
        h1 = soup.find("h1")
        if h1:
            title = h1.get_text(" ", strip=True)

    if not title:
        title = url

    return clean_display_text(title)


def extract_date_candidates(text):
    """
    Türkçe tarih biçimlerini yakalar:
    01.10.2026
    01/10/2026
    01-10-2026
    """

    patterns = [
        r"\b(\d{1,2})[./-](\d{1,2})[./-](20\d{2})\b"
    ]

    results = []

    for pattern in patterns:
        for m in re.finditer(pattern, text):
            try:
                day = int(m.group(1))
                month = int(m.group(2))
                year = int(m.group(3))

                date_obj = datetime(year, month, day).date()

                results.append(date_obj)

            except Exception:
                continue

    return sorted(set(results))


def extract_deadline(text):
    """
    İlan metninde 'son başvuru', 'başvuru süresi', vb.
    ifadelerin çevresindeki tarihleri bulmaya çalışır.
    """

    text_clean = clean_display_text(text)

    patterns = [
        r"son başvuru.{0,250}",
        r"son basvuru.{0,250}",
        r"başvuru süresi.{0,250}",
        r"basvuru suresi.{0,250}",
        r"başvurular.{0,250}",
        r"basvurular.{0,250}",
        r"başvuruların son günü.{0,250}",
        r"basvurularin son gunu.{0,250}"
    ]

    candidates = []

    lower = normalize_text(text_clean)

    for pattern in patterns:
        for m in re.finditer(pattern, lower):
            piece = text_clean[m.start():m.end()]
            candidates.extend(extract_date_candidates(piece))

    if candidates:
        return max(candidates)

    return None


def extract_kpss_minimum(text):
    """
    Örnekleri yakalamaya çalışır:

    KPSS P3 70
    KPSSP3 70
    KPSS P3 puan türünden en az 70
    KPSSP3 puanından en az 60
    """

    normalized = normalize_text(text)

    patterns = [
        r"kpss\s*p\s*3.{0,100}?(?:en az|asgari|taban|puanı|puani)?\s*[:\-]?\s*(\d{2}(?:[.,]\d+)?)",
        r"kpssp3.{0,100}?(?:en az|asgari|puanı|puani)?\s*[:\-]?\s*(\d{2}(?:[.,]\d+)?)",
        r"kpss\s*p\s*3.{0,100}?(\d{2}(?:[.,]\d+)?)"
    ]

    values = []

    for pattern in patterns:
        for match in re.finditer(pattern, normalized):
            try:
                value = float(match.group(1).replace(",", "."))
                if 40 <= value <= 100:
                    values.append(value)
            except Exception:
                continue

    if not values:
        return None

    return max(values)


def extract_kpss_types(text):
    normalized = normalize_text(text)

    found = []

    patterns = [
        r"kpss\s*p\s*([123])",
        r"kpssp([123])",
        r"\bp(93|94|121)\b",
        r"\bp(48)\b"
    ]

    for pattern in patterns:
        for match in re.finditer(pattern, normalized):
            value = match.group(1)

            if value in ["1", "2", "3"]:
                value = f"P{value}"
            else:
                value = f"P{value}"

            if value not in found:
                found.append(value)

    return found


def extract_qualification_codes(text):
    """
    ÖSYM/KPSS nitelik kodu formatlarını yakalar.
    Örnek:
    4431
    6225
    4421, 4459, 6225
    """

    codes = re.findall(r"\b(3\d{3}|4\d{3}|6\d{3}|7\d{3})\b", text)

    return sorted(set(codes))


# ============================================================
# UYGUNLUK MOTORU
# ============================================================

def evaluate_job(job, profile):
    """
    Her ilan için:
    GREEN  -> büyük ölçüde uygun
    YELLOW -> incelenmesi gerekiyor
    RED    -> açıkça uygun değil
    """

    text = normalize_text(
        f"{job.get('title', '')} {job.get('text', '')}"
    )

    score = 0
    reasons = []
    warnings = []

    # --------------------------------------------------------
    # 1. KPSS PUAN TÜRÜ
    # --------------------------------------------------------

    detected_kpss_types = extract_kpss_types(text)

    desired_type = profile["kpss_type"]

    if desired_type in detected_kpss_types:
        score += 25
        reasons.append(f"KPSS {desired_type} şartı tespit edildi.")

    elif detected_kpss_types:
        warnings.append(
            "İlanda farklı bir KPSS puan türü belirtilmiş: "
            + ", ".join(detected_kpss_types)
        )

    # --------------------------------------------------------
    # 2. KPSS MİNİMUM PUANI
    # --------------------------------------------------------

    minimum_score = extract_kpss_minimum(text)

    if minimum_score is not None:

        if profile["kpss_score"] >= minimum_score:
            score += 30

            reasons.append(
                f"KPSS puanın {profile['kpss_score']}, "
                f"ilan minimumu {minimum_score}."
            )

        else:
            return {
                "verdict": "🔴 UYGUN DEĞİL",
                "score": 0,
                "reasons": [
                    f"KPSS puanı yetersiz: "
                    f"{profile['kpss_score']} < {minimum_score}"
                ],
                "warnings": [],
                "minimum_kpss": minimum_score
            }

    else:
        warnings.append("KPSS minimum puanı metinden net çıkarılamadı.")

    # --------------------------------------------------------
    # 3. MEZUNİYET / BÖLÜM
    # --------------------------------------------------------

    department_hits = keyword_hits(
        text,
        profile["departments"]
    )

    if department_hits:
        score += 30

        reasons.append(
            "Bölümünle eşleşen ifade bulundu: "
            + ", ".join(department_hits[:4])
        )

    else:

        if contains_any(text, GENERAL_LICENSE_WORDS):
            score += 15
            reasons.append(
                "İlanda genel lisans mezuniyeti şartı tespit edildi."
            )

        elif contains_any(text, [
            "herhangi bir yükseköğretim",
            "herhangi bir fakülte",
            "fakülte veya yüksekokul"
        ]):
            score += 10

            reasons.append(
                "İlanda geniş lisans/yükseköğretim şartı görülüyor."
            )

        else:
            warnings.append(
                "SBKY/Kamu Yönetimi mezuniyeti açık biçimde bulunamadı."
            )

    # --------------------------------------------------------
    # 4. NİTELİK KODLARI
    # --------------------------------------------------------

    found_codes = extract_qualification_codes(text)

    user_codes = set(
        str(x).strip()
        for x in profile["qualification_codes"]
        if str(x).strip()
    )

    matching_codes = sorted(
        user_codes.intersection(set(found_codes))
    )

    if matching_codes:

        score += 35

        reasons.append(
            "Eşleşen nitelik kodu: "
            + ", ".join(matching_codes)
        )

    elif found_codes:
        warnings.append(
            "İlanda nitelik kodları bulundu: "
            + ", ".join(found_codes[:12])
        )

    # --------------------------------------------------------
    # 5. BİLGİSAYAR SERTİFİKASI
    # --------------------------------------------------------

    if contains_any(text, CERTIFICATE_KEYWORDS):

        if profile["has_computer_certificate"]:
            score += 15
            reasons.append(
                "Bilgisayar sertifikası/belgesi şartı profilinle eşleşebilir."
            )

        else:
            warnings.append(
                "İlanda bilgisayar sertifikası şartı bulunuyor."
            )

    # --------------------------------------------------------
    # 6. HEDEF POZİSYON
    # --------------------------------------------------------

    job_hits = keyword_hits(
        text,
        profile["target_jobs"]
    )

    if job_hits:
        score += 10

        reasons.append(
            "Hedef pozisyonlardan biri bulundu: "
            + ", ".join(job_hits[:5])
        )

    # --------------------------------------------------------
    # 7. KPSS YILI
    # --------------------------------------------------------

    if profile["kpss_year"]:

        year_text = str(profile["kpss_year"])

        if year_text in text and "kpss" in text:
            score += 5
            reasons.append(
                f"{profile['kpss_year']} KPSS yılı metinde geçiyor."
            )

    # --------------------------------------------------------
    # 8. SON KARAR
    # --------------------------------------------------------

    if score >= 55 and len(warnings) <= 2:
        verdict = "🟢 BÜYÜK OLASILIKLA UYGUN"

    elif score >= 30:
        verdict = "🟡 KONTROL ET"

    else:
        verdict = "🟡 KONTROL ET"

    return {
        "verdict": verdict,
        "score": min(score, 100),
        "reasons": reasons,
        "warnings": warnings,
        "minimum_kpss": minimum_score
    }


# ============================================================
# KAYNAK TARAMA
# ============================================================

def recruitment_score(text):
    normalized = normalize_text(text)

    score = 0

    for keyword in RECRUITMENT_KEYWORDS:
        if normalize_text(keyword) in normalized:
            score += 1

    return score


def extract_links(html, current_url):
    soup = BeautifulSoup(html, "lxml")

    links = []

    for a in soup.find_all("a", href=True):

        href = a.get("href", "").strip()

        if not href:
            continue

        full_url = urljoin(current_url, href)
        full_url = canonical_url(full_url)

        if not full_url:
            continue

        if urlparse(full_url).scheme not in ("http", "https"):
            continue

        if not same_domain(current_url, full_url):
            continue

        label = clean_display_text(
            a.get_text(" ", strip=True)
        )

        combined = normalize_text(
            f"{label} {full_url}"
        )

        priority = 0

        for keyword in RECRUITMENT_KEYWORDS:
            if normalize_text(keyword) in combined:
                priority += 10

        if "pdf" in combined:
            priority += 3

        if "ilan" in combined:
            priority += 5

        if "personel" in combined:
            priority += 10

        if "kpss" in combined:
            priority += 15

        links.append(
            (priority, full_url, label)
        )

    # En ilgili bağlantıları önce tarayacağız.
    links.sort(
        key=lambda x: x[0],
        reverse=True
    )

    # Aynı URL'yi tekilleştir.
    unique = []
    seen = set()

    for item in links:
        if item[1] in seen:
            continue

        seen.add(item[1])
        unique.append(item)

    return unique


def parse_document(content, content_type, url):
    """
    PDF veya HTML belgeden:
    title + text + links döndürür.
    """

    if content_type == "pdf":

        text = extract_pdf_text(content)

        title = url.split("/")[-1]

        return {
            "title": clean_display_text(title),
            "text": text,
            "links": []
        }

    soup = BeautifulSoup(content, "lxml")

    # Gereksiz alanları kaldır.
    for element in soup([
        "script",
        "style",
        "noscript",
        "svg",
        "footer"
    ]):
        element.decompose()

    title = extract_title(soup, url)

    text = clean_display_text(
        soup.get_text(" ", strip=True)
    )

    links = extract_links(
        content,
        url
    )

    return {
        "title": title,
        "text": text,
        "links": links
    }


def crawl_source(source, max_total_pages=None):
    """
    Bir kaynak içerisinde kontrollü BFS/priority crawl.
    """

    max_pages = max_total_pages or source.max_pages

    start_url = canonical_url(source.url)

    if not start_url:
        return [], ["Geçersiz başlangıç adresi"]

    queue = []

    # heap:
    # (-priority, depth, url)
    heapq.heappush(
        queue,
        (-100, 0, start_url)
    )

    seen = set()
    results = []
    errors = []

    pages_scanned = 0

    while queue and pages_scanned < max_pages:

        _, depth, current_url = heapq.heappop(queue)

        if current_url in seen:
            continue

        seen.add(current_url)

        if depth > 2:
            continue

        time.sleep(DEFAULT_DELAY)

        content, content_type, error = fetch_url(
            current_url
        )

        if error:
            errors.append(
                f"{current_url} -> {error}"
            )
            continue

        pages_scanned += 1

        parsed = parse_document(
            content,
            content_type,
            current_url
        )

        title = parsed["title"]
        text = parsed["text"]

        rel_score = recruitment_score(
            f"{title} {text[:30000]}"
        )

        # Aranan ilan kelimeleri varsa kaydet.
        if rel_score >= 2:
            record = {
                "source": source.name,
                "title": title,
                "url": current_url,
                "text": text,
                "recruitment_score": rel_score,
                "scanned_at": datetime.now().strftime(
                    "%d.%m.%Y %H:%M:%S"
                )
            }

            results.append(record)

        # HTML bağlantılarını kuyruğa koy.
        for priority, next_url, label in parsed["links"]:

            if next_url in seen:
                continue

            # Çok genel navigation bağlantılarını
            # gereksiz yere taramamak için alt sınır.
            effective_priority = priority

            # Derinlik cezası.
            effective_priority -= depth * 2

            if effective_priority < 0:
                effective_priority = 0

            heapq.heappush(
                queue,
                (-effective_priority, depth + 1, next_url)
            )

    return results, errors


# ============================================================
# SONUÇLARI TEKİLLEŞTİRME
# ============================================================

def deduplicate_jobs(jobs):
    unique = {}
    seen_fingerprints = set()

    for job in jobs:

        title = normalize_text(
            job.get("title", "")
        )

        url = job.get("url", "")

        fingerprint = (
            title[:250],
            hostname(url),
            extract_deadline(job.get("text", "")),
        )

        if fingerprint in seen_fingerprints:
            continue

        seen_fingerprints.add(fingerprint)

        unique[stable_id(url, title)] = job

    return list(unique.values())


# ============================================================
# TARİH / DURUM
# ============================================================

def deadline_status(deadline):
    if not deadline:
        return "Bilinmiyor"

    today = datetime.now().date()

    delta = (deadline - today).days

    if delta < 0:
        return "🔴 Süresi geçmiş"

    if delta == 0:
        return "🔴 SON GÜN"

    if delta <= 3:
        return f"🟠 {delta} gün kaldı"

    if delta <= 7:
        return f"🟡 {delta} gün kaldı"

    return f"🟢 {delta} gün kaldı"


# ============================================================
# STREAMLIT ARAYÜZ
# ============================================================

st.title("🎯 KPSS İlan Avcısı")

st.markdown(
    """
    **Kamu personel ilanlarını tara → şartları analiz et → "
    "profilime uygun olanları göster.**
    """
)

st.info(
    "Bu sistem ilanı senin yerine başvurmaz. "
    "Resmî ilanı bulur, şartları analiz eder ve "
    "başvuru bağlantısını gösterir."
)


# ============================================================
# SIDEBAR - PROFİL
# ============================================================

st.sidebar.header("👤 Aday Profili")

kpss_score = st.sidebar.number_input(
    "KPSS puanın",
    min_value=0.0,
    max_value=100.0,
    value=74.0,
    step=0.01
)

kpss_type = st.sidebar.selectbox(
    "KPSS puan türün",
    KPSSTYPES,
    index=2
)

kpss_year = st.sidebar.number_input(
    "KPSS yılı",
    min_value=2000,
    max_value=datetime.now().year,
    value=2024,
    step=1
)

education_level = st.sidebar.selectbox(
    "Öğrenim düzeyi",
    ["Lisans", "Ön Lisans", "Ortaöğretim"],
    index=0
)

departments_text = st.sidebar.text_area(
    "Bölüm / mezuniyet ifadeleri",
    value=(
        "Siyaset Bilimi ve Kamu Yönetimi\n"
        "Siyaset Bilimi ve Kamu Yönetimi Bölümü\n"
        "Kamu Yönetimi\n"
        "Siyaset Bilimi\n"
        "İktisadi ve İdari Bilimler Fakültesi\n"
        "İİBF"
    ),
    height=160
)

qualification_codes_text = st.sidebar.text_input(
    "Bildigin nitelik kodları",
    value="6225"
)

has_computer_certificate = st.sidebar.checkbox(
    "Bilgisayar sertifikam/belgem var",
    value=True
)

cities_text = st.sidebar.text_input(
    "Tercih edilen iller",
    value="Ankara, Konya"
)

target_jobs_text = st.sidebar.text_area(
    "Aradığın pozisyonlar",
    value=(
        "memur\n"
        "büro personeli\n"
        "büro görevlisi\n"
        "veri hazırlama ve kontrol işletmeni\n"
        "bilgisayar işletmeni\n"
        "uzman yardımcısı\n"
        "personel"
    ),
    height=160
)


# ============================================================
# PROFİL SÖZLÜĞÜ
# ============================================================

profile = {
    "kpss_score": float(kpss_score),
    "kpss_type": kpss_type,
    "kpss_year": int(kpss_year),
    "education_level": education_level,

    "departments": [
        x.strip()
        for x in departments_text.splitlines()
        if x.strip()
    ],

    "qualification_codes": [
        x.strip()
        for x in re.split(r"[,;\s]+", qualification_codes_text)
        if x.strip()
    ],

    "has_computer_certificate":
        has_computer_certificate,

    "cities": [
        x.strip()
        for x in re.split(r"[,;]+", cities_text)
        if x.strip()
    ],

    "target_jobs": [
        x.strip()
        for x in target_jobs_text.splitlines()
        if x.strip()
    ]
}


# ============================================================
# KAYNAKLAR
# ============================================================

st.sidebar.header("🌐 Tarama Kaynakları")

sources = []

for default_source in DEFAULT_SOURCES:

    enabled = st.sidebar.checkbox(
        default_source.name,
        value=default_source.enabled,
        key=f"source_{default_source.name}"
    )

    pages = st.sidebar.number_input(
        f"{default_source.name} - maksimum sayfa",
        min_value=5,
        max_value=200,
        value=default_source.max_pages,
        step=5,
        key=f"pages_{default_source.name}"
    )

    sources.append(
        Source(
            default_source.name,
            default_source.url,
            enabled,
            int(pages)
        )
    )


# ============================================================
# ÖZEL KAMU KURUMLARI
# ============================================================

st.sidebar.subheader("➕ Ek kamu sitesi")

custom_sources_text = st.sidebar.text_area(
    "Taransın istediğin kurum siteleri",
    value=(
        "https://www.adalet.gov.tr/\n"
        "https://www.sbb.gov.tr/\n"
        "https://www.yok.gov.tr/"
    ),
    height=120
)

custom_pages = st.sidebar.number_input(
    "Ek sitelerde kaynak başına maksimum sayfa",
    min_value=5,
    max_value=100,
    value=20,
    step=5
)

custom_urls = [
    x.strip()
    for x in custom_sources_text.splitlines()
    if x.strip()
]

for i, url in enumerate(custom_urls):

    sources.append(
        Source(
            f"Özel Kaynak {i+1}",
            url,
            True,
            int(custom_pages)
        )
    )


# ============================================================
# FİLTRELER
# ============================================================

st.sidebar.header("🔎 Sonuç Filtreleri")

hide_expired = st.sidebar.checkbox(
    "Süresi geçmiş ilanları gizle",
    value=True
)

only_kpss = st.sidebar.checkbox(
    "Sadece KPSS geçen ilanları göster",
    value=False
)

only_target_jobs = st.sidebar.checkbox(
    "Hedef pozisyonlarımı içerenleri öne çıkar",
    value=True
)

minimum_match_score = st.sidebar.slider(
    "Minimum uygunluk skoru",
    min_value=0,
    max_value=100,
    value=20,
    step=5
)


# ============================================================
# ARA BUTONU
# ============================================================

search_button = st.button(
    "🔎 İLANLARI ARA",
    type="primary",
    use_container_width=True
)


# ============================================================
# TARAMA
# ============================================================

if search_button:

    active_sources = [
        s for s in sources
        if s.enabled
    ]

    if not active_sources:

        st.error(
            "En az bir tarama kaynağı seçmelisin."
        )

        st.stop()

    all_jobs = []
    all_errors = []

    progress = st.progress(0)

    status_box = st.empty()

    total_sources = len(active_sources)

    for index, source in enumerate(active_sources):

        status_box.info(
            f"🔍 Taranıyor: {source.name}"
        )

        try:

            jobs, errors = crawl_source(
                source,
                max_total_pages=source.max_pages
            )

            all_jobs.extend(jobs)
            all_errors.extend(errors)

        except Exception as e:

            all_errors.append(
                f"{source.name}: {str(e)}"
            )

        progress.progress(
            int(((index + 1) / total_sources) * 100)
        )

    status_box.success(
        f"Tarama tamamlandı. "
        f"{len(all_jobs)} potansiyel ilan sayfası bulundu."
    )

    # --------------------------------------------------------
    # TEKİLLEŞTİR
    # --------------------------------------------------------

    all_jobs = deduplicate_jobs(
        all_jobs
    )

    analyzed_jobs = []

    # --------------------------------------------------------
    # UYGUNLUK ANALİZİ
    # --------------------------------------------------------

    for job in all_jobs:

        evaluation = evaluate_job(
            job,
            profile
        )

        text = normalize_text(
            job["title"] + " " + job["text"]
        )

        deadline = extract_deadline(
            job["text"]
        )

        deadline_state = deadline_status(
            deadline
        )

        # ----------------------------------------------------
        # Süresi geçmiş filtre
        # ----------------------------------------------------

        if (
            hide_expired
            and deadline
            and deadline < datetime.now().date()
        ):
            continue

        # ----------------------------------------------------
        # KPSS filtresi
        # ----------------------------------------------------

        if only_kpss and "kpss" not in text:
            continue

        # ----------------------------------------------------
        # Uygunluk skoru
        # ----------------------------------------------------

        if (
            evaluation["score"] < minimum_match_score
        ):
            continue

        # ----------------------------------------------------
        # Hedef pozisyon
        # ----------------------------------------------------

        target_hits = keyword_hits(
            text,
            profile["target_jobs"]
        )

        analyzed_jobs.append({
            "Durum": evaluation["verdict"],
            "Skor": evaluation["score"],
            "Kaynak": job["source"],
            "İlan": job["title"],
            "Son Başvuru": (
                deadline.strftime("%d.%m.%Y")
                if deadline else
                "Belirlenemedi"
            ),
            "Başvuru Durumu": deadline_state,
            "KPSS Minimum": (
                evaluation["minimum_kpss"]
                if evaluation["minimum_kpss"] is not None
                else "-"
            ),
            "Hedef Pozisyon": (
                ", ".join(target_hits[:4])
                if target_hits else "-"
            ),
            "Neden Uygun?": " ".join(
                evaluation["reasons"]
            ),
            "Kontrol Edilecek": " ".join(
                evaluation["warnings"]
            ),
            "URL": job["url"]
        })

    # --------------------------------------------------------
    # DATAFRAME
    # --------------------------------------------------------

    df = pd.DataFrame(
        analyzed_jobs
    )

    if df.empty:

        st.warning(
            "Filtrelere uyan ilan bulunamadı."
        )

        if all_errors:

            with st.expander(
                "Tarama sırasında oluşan teknik kayıtlar"
            ):
                for error in all_errors[:50]:
                    st.write(error)

        st.stop()

    # --------------------------------------------------------
    # SIRALAMA
    # --------------------------------------------------------

    status_order = {
        "🔴 SON GÜN": 0,
        "🟠": 1,
        "🟡": 2,
        "🟢": 3
    }

    df = df.sort_values(
        by=["Skor"],
        ascending=False
    )

    # --------------------------------------------------------
    # ÜST İSTATİSTİKLER
    # --------------------------------------------------------

    green_count = len(
        df[
            df["Durum"]
            .str.contains("🟢", na=False)
        ]
    )

    yellow_count = len(
        df[
            df["Durum"]
            .str.contains("🟡", na=False)
        ]
    )

    red_count = len(
        df[
            df["Durum"]
            .str.contains("🔴", na=False)
        ]
    )

    c1, c2, c3, c4 = st.columns(4)

    c1.metric(
        "Bulunan ilan",
        len(df)
    )

    c2.metric(
        "Büyük olasılıkla uygun",
        green_count
    )

    c3.metric(
        "Kontrol edilmeli",
        yellow_count
    )

    c4.metric(
        "Riskli / uygun değil",
        red_count
    )

    # --------------------------------------------------------
    # SADECE UYGUN İLANLAR
    # --------------------------------------------------------

    st.subheader(
        "🎯 Sana uygun olabilecek ilanlar"
    )

    preferred_df = df[
        df["Durum"].str.contains(
            "🟢|🟡",
            regex=True,
            na=False
        )
    ].copy()

    if not preferred_df.empty:

        st.dataframe(
            preferred_df[
                [
                    "Durum",
                    "Skor",
                    "Kaynak",
                    "İlan",
                    "Son Başvuru",
                    "Başvuru Durumu",
                    "KPSS Minimum",
                    "Hedef Pozisyon",
                    "Neden Uygun?",
                    "Kontrol Edilecek",
                    "URL"
                ]
            ],
            use_container_width=True,
            hide_index=True,
            column_config={
                "URL": st.column_config.LinkColumn(
                    "Resmî İlan",
                    display_text="İLANI AÇ"
                ),
                "Skor": st.column_config.ProgressColumn(
                    "Uygunluk",
                    min_value=0,
                    max_value=100,
                    format="%d"
                )
            }
        )

    else:

        st.info(
            "Şu anda açıkça uygun görünen ilan yok."
        )

    # --------------------------------------------------------
    # TÜM SONUÇLAR
    # --------------------------------------------------------

    with st.expander(
        "📋 Tüm tarama sonuçlarını göster"
    ):

        st.dataframe(
            df[
                [
                    "Durum",
                    "Skor",
                    "Kaynak",
                    "İlan",
                    "Son Başvuru",
                    "Başvuru Durumu",
                    "KPSS Minimum",
                    "Hedef Pozisyon",
                    "Neden Uygun?",
                    "Kontrol Edilecek",
                    "URL"
                ]
            ],
            use_container_width=True,
            hide_index=True,
            column_config={
                "URL": st.column_config.LinkColumn(
                    "İlan",
                    display_text="AÇ"
                )
            }
        )

    # --------------------------------------------------------
    # CSV İNDİR
    # --------------------------------------------------------

    csv_data = df.to_csv(
        index=False,
        encoding="utf-8-sig"
    )

    st.download_button(
        "📥 Sonuçları Excel/CSV olarak indir",
        data=csv_data,
        file_name=(
            "kpss_ilan_sonuclari_"
            + datetime.now().strftime("%Y%m%d_%H%M")
            + ".csv"
        ),
        mime="text/csv",
        use_container_width=True
    )

    # --------------------------------------------------------
    # TEKNİK HATALAR
    # --------------------------------------------------------

    if all_errors:

        with st.expander(
            "⚠️ Erişilemeyen / taranamayan sayfalar"
        ):

            for error in all_errors[:100]:
                st.write(error)

    st.caption(
        "Not: Uygunluk motoru ilan metnini otomatik yorumlar. "
        "Kesin başvuru hakkı için her zaman ilanın kendi "
        "resmî şartnamesi esas alınmalıdır."
    )


# ============================================================
# İLK AÇILIŞ EKRANI
# ============================================================

if not search_button:

    st.markdown(
        """
        ### Sistem nasıl çalışıyor?

        **1. Profilini tanımlıyorsun.**

        KPSS puanın, puan türün, bölümün, sertifikaların ve
        aradığın kadrolar sisteme giriliyor.

        **2. “İLANLARI ARA” butonuna basıyorsun.**

        Seçtiğin resmî kaynaklar kontrollü şekilde taranıyor.

        **3. İlan metinleri analiz ediliyor.**

        Sistem KPSS puanı, KPSS puan türü, bölüm, nitelik kodları,
        bilgisayar belgesi, pozisyon ve başvuru tarihlerini arıyor.

        **4. Sonuç sana göre sıralanıyor.**

        🟢 Büyük olasılıkla uygun

        🟡 Kontrol et

        🔴 Açıkça uygun değil

        **5. İlanın resmî sayfasını doğrudan açabiliyorsun.**
        """
    )

    st.warning(
        "Özellikle nitelik kodları ve özel şartlarda otomatik analiz "
        "yardımcıdır; son kontrol mutlaka resmî ilan metninden yapılmalıdır."
    )
