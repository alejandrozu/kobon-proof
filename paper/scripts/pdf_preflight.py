"""Structural PDF checks; these supplement, rather than replace, visual review.

Only pypdf and the Python standard library are required. ``audit_pdf(path)``
returns a JSON-serializable report on success and raises ``PDFPreflightError``
with the same report in ``error.report`` on failure. Missing ToUnicode maps are
reported as an extraction/accessibility limitation, not a visual font failure.
"""
from pathlib import Path
import hashlib
import json
import math
import re
import sys

from pypdf import PdfReader


class PDFPreflightError(ValueError):
    def __init__(self, report):
        self.report = report
        super().__init__("PDF preflight failed: " + "; ".join(report["errors"]))


def _resolve(value):
    return value.get_object() if hasattr(value, "get_object") else value


def _object_key(value):
    reference = getattr(value, "indirect_reference", None)
    reference = value if hasattr(value, "idnum") else reference
    if reference is not None:
        return f"{reference.idnum} {reference.generation} R"
    return f"direct:{id(value)}"


def audit_pdf(path):
    """Check embedded fonts, extracted text and page boxes; return a report.

    Type 3 fonts store glyph programs in CharProcs and are accepted explicitly.
    The scan follows nested XObject and Type 3 resources. Intentional square
    symbols (including proof-end marks) are not treated as missing glyphs.
    """
    path = Path(path)
    report = {
        "passed": False,
        "pdf": path.name,
        "pdf_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "scope": "Structural and text-extraction checks, not visual rendering verification.",
        "page_count": 0,
        "pages": [],
        "fonts": [],
        "missing_to_unicode": [],
        "errors": [],
    }
    errors = report["errors"]
    fonts = {}
    reader = PdfReader(path)
    report["page_count"] = len(reader.pages)
    if not reader.pages:
        errors.append("PDF has no pages")

    def font_record(reference, page_number):
        key = _object_key(reference)
        font = _resolve(reference)
        if key in fonts:
            record = fonts[key]
            if page_number not in record["pages"]:
                record["pages"].append(page_number)
            return
        subtype = str(font.get("/Subtype", "unknown"))
        record = {
            "object": key,
            "name": str(font.get("/BaseFont", "unnamed")),
            "subtype": subtype,
            "pages": [page_number],
            "embedded": False,
            "to_unicode": bool(font.get("/ToUnicode")),
            "embedding": [],
        }
        fonts[key] = record
        if subtype == "/Type3":
            programs = _resolve(font.get("/CharProcs"))
            # An empty glyph program can legitimately represent a blank space.
            record["embedded"] = bool(programs) and all(
                hasattr(_resolve(program), "get_data") for program in programs.values()
            )
            record["embedding"].append("Type 3 CharProcs glyph programs")
        else:
            descendants = _resolve(font.get("/DescendantFonts"))
            parts = list(descendants) if subtype == "/Type0" and descendants else [font]
            embedded = []
            for part in parts:
                part = _resolve(part)
                descriptor = _resolve(part.get("/FontDescriptor")) or {}
                streams = []
                for field in ("/FontFile", "/FontFile2", "/FontFile3"):
                    if field in descriptor:
                        stream = _resolve(descriptor[field])
                        if hasattr(stream, "get_data") and stream.get_data():
                            streams.append(field)
                embedded.append(bool(streams))
                record["embedding"].extend(streams)
            record["embedded"] = bool(embedded) and all(embedded)
        if not record["embedded"]:
            errors.append(f"Font {record['name']} ({key}) lacks embedded font or glyph programs")

    def walk_resources(resources, page_number, visited):
        if resources is None:
            return
        key = _object_key(resources)
        if key in visited:
            return
        visited.add(key)
        resources = _resolve(resources)
        for reference in (_resolve(resources.get("/Font")) or {}).values():
            font_record(reference, page_number)
            font = _resolve(reference)
            if font.get("/Subtype") == "/Type3":
                walk_resources(font.get("/Resources"), page_number, visited)
        for reference in (_resolve(resources.get("/XObject")) or {}).values():
            obj = _resolve(reference)
            walk_resources(obj.get("/Resources"), page_number, visited)

    for page_number, page in enumerate(reader.pages, start=1):
        boxes = {}
        for name, box in (("media_box", page.mediabox), ("crop_box", page.cropbox)):
            values = [float(value) for value in box]
            boxes[name] = values
            if not (all(math.isfinite(value) for value in values)
                    and values[2] > values[0] and values[3] > values[1]):
                errors.append(f"Page {page_number} has invalid {name} geometry")
        user_unit = float(page.get("/UserUnit", 1))
        if not math.isfinite(user_unit) or user_unit <= 0:
            errors.append(f"Page {page_number} has invalid UserUnit")
        try:
            text = page.extract_text() or ""
        except Exception as exc:
            errors.append(f"Page {page_number} text extraction failed: {type(exc).__name__}")
            text = ""
        if not text.strip():
            errors.append(f"Page {page_number} has no extractable text")
        for character, description in (("\ufffd", "U+FFFD replacement character"),
                                       ("\x00", "NUL character")):
            if character in text:
                errors.append(f"Page {page_number} contains {description} in extracted text")
        placeholders = sorted(set(re.findall(r"\.notdef\b|\(cid:\d+\)", text)))
        if placeholders:
            errors.append(f"Page {page_number} contains extraction placeholders: {placeholders}")
        report["pages"].append({
            "page": page_number, "text_characters": len(text),
            "user_unit": user_unit, **boxes,
        })
        walk_resources(page.get("/Resources"), page_number, set())

    report["fonts"] = list(fonts.values())
    report["font_count"] = len(fonts)
    report["missing_to_unicode"] = [
        {"object": font["object"], "name": font["name"]}
        for font in fonts.values() if not font["to_unicode"]
    ]
    report["missing_to_unicode_note"] = (
        "Missing ToUnicode maps may limit extraction or accessibility; "
        "they do not by themselves establish a visual rendering fault."
    )
    report["passed"] = not errors
    if errors:
        raise PDFPreflightError(report)
    return report


if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("Usage: python pdf_preflight.py PATH.pdf")
    try:
        result = audit_pdf(sys.argv[1])
    except PDFPreflightError as error:
        print(json.dumps(error.report, indent=2))
        raise SystemExit(1)
    print(json.dumps(result, indent=2))
