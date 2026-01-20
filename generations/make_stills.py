from PIL import Image, ImageDraw, ImageFont
import textwrap
from pathlib import Path

PROMPTS_FILE = Path("generations/audio_prompts.txt")
OUT_DIR = Path("generations")
OUT_DIR.mkdir(exist_ok=True)

if not PROMPTS_FILE.exists():
    print("Prompts file not found:", PROMPTS_FILE)
    raise SystemExit(1)

lines = [l.strip() for l in PROMPTS_FILE.read_text(encoding='utf-8').splitlines() if l.strip()]

W = 1920
H = 1080
MARGIN = 80
FONT_SIZE = 44

try:
    font = ImageFont.truetype("/Library/Fonts/Arial.ttf", FONT_SIZE)
except Exception:
    try:
        font = ImageFont.truetype("DejaVuSans.ttf", FONT_SIZE)
    except Exception:
        from PIL import ImageFont as _IF
        font = _IF.load_default()

for i, text in enumerate(lines):
    img = Image.new("RGB", (W, H), color=(8, 8, 8))
    draw = ImageDraw.Draw(img)

    # Wrap body text
    body = text
    max_width = W - 2 * MARGIN
    lines_wrapped = textwrap.wrap(body, width=60)

    # Start text a bit down from top margin (no title)
    y = MARGIN + 40
    for ln in lines_wrapped:
        draw.text((MARGIN, y), ln, font=font, fill=(240, 240, 240))
        y += FONT_SIZE + 12

    out_path = OUT_DIR / f"zombies_{i:02d}.png"
    img.save(out_path)
    print("Wrote", out_path)
