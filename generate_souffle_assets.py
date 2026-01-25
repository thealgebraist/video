import torch
import torch.multiprocessing as mp
import os
import numpy as np
import scipy.io.wavfile as wavfile
import argparse
import utils
import gc
import subprocess
from diffusers import StableDiffusion3Pipeline, StableAudioPipeline
from PIL import Image

# --- Configuration & Defaults ---
PROJECT_NAME = "souffle"
ASSETS_DIR = f"assets_{PROJECT_NAME}"
DEVICE = (
    "cuda"
    if torch.cuda.is_available()
    else ("mps" if torch.backends.mps.is_available() else "cpu")
)

# Using SD3.5 Large for maximum quality as requested.
DEFAULT_MODEL = "stabilityai/stable-diffusion-3.5-large"
DEFAULT_STEPS = 40
DEFAULT_GUIDANCE = 4.5

# High-fidelity Cyber-Noir Prompt Suffix
PROMPT_SUFFIX = ", Cinematic lighting, Arri Alexa 65, anamorphic lens, 8k, bokeh, color graded in teal and orange, hyper-realistic textures, ray-tracing, volumetric fog, shot on 35mm film"

# 32 Scenes for THE ASCENT
SCENES = [
    ("01_kitchen", "Ultra-wide shot of a dark brutalist kitchen, cold teal shadows, obsidian black marble surfaces reflecting a sharp bioluminescent blue LED line, volumetric smoke caught in light", "distant wind howling through a vent"),
    ("02_sweat", "Extreme Close-up of a crystalline bead of sweat on a temple, skin texture hyper-detailed with visible pores, harsh amber rim-lighting, deep teal skin tones", "slow wet heartbeat"),
    ("03_whisk", "Macro of a hand in black nitrile glove gripping a heavy brushed-steel whisk, cold metal reflecting an orange spark, tight matte glove texture", "leather-on-metal creak"),
    ("04_ramekin", "Medium shot of a white ceramic ramekin on a black obsidian slab, lone pillar in a void, sharp contrast, rim-lit, deep teal ambient shadows", "low industrial hum"),
    ("05_start_button", "Close-up of a finger over a glowing amber Start haptic icon on a futuristic touch-screen, fine grain screen texture, micro-scratches", "high-pitched electric whine"),
    ("06_egg_crack", "Extreme Macro of an eggshell fracturing like a tectonic canyon, calcium-white texture, golden yolk oozing like molten lava, pitch-black background", "bone-dry crack"),
    ("07_chocolate", "View into a copper bowl of swirling dark chocolate ganache, obsidian whirlpool, glossy viscous surface, moody teal reflections", "thick viscous gurgle"),
    ("08_arthur_profile", "Man face split by Rembrandt lighting, one side in oppressive black, the other in harsh bioluminescent amber glow, intense bloodshot stare", "sharp intake of breath"),
    ("09_egg_whites", "Macro of whisking egg whites, translucent and viscous, reflecting blue moonlight and sharp cyan highlights, star-like air bubbles", "rhythmic metallic clashing"),
    ("10_clock", "POV through a cloud of sifted flour, digital clock with red LED numbers glowing through white dust, powdery texture", "distorted heavy ticking"),
    ("11_nebula", "Abstract flour particles suspended like stars in a nebula, sharp horizontal amber side-light, deep teal background", "whirring wind"),
    ("12_folding", "Macro of rubber spatula folding foam, texture of torn velvet, deep shadows in aerated folds, matte rubber vs glossy batter", "soft wet tear"),
    ("13_eye_reflect", "Close-up of an eye pupil as an obsidian black hole reflecting glowing orange-red heating coils, detailed iris textures", "fire roar muffled"),
    ("14_rim_wipe", "Thumb wiping a clinical porcelain-white ramekin rim, perfectly smooth ceramic surface, fine thumb skin ridges", "sharp squeak"),
    ("15_tray_slide", "Close-up of a gloved hand trembling, sliding a tray into a pitch-black oven maw, amber light leaking from edges", "fabric-on-metal friction"),
    ("16_door_seal", "Oven door sealing with a heavy mechanical latch, bioluminescent blue vacuum seal light, industrial hardware", "hydraulic thud"),
    ("17_tectonic", "Abstract shot of soufflé batter expanding under heat, taut skin stretching like a drum, micro-cracks in the crust", "growing tectonic groan"),
    ("18_vibration", "Macro of ramekin vibrating on metal rack, glowing cherry-red wires, scorched ceramic base textures", "violent metallic rattling"),
    ("19_steam_vent", "Extreme Macro of a tiny steam vent in a soufflé crust, high-pressure vapor in a sliver of amber light", "high-pressure hiss"),
    ("20_arthur_burn", "Man's face lit by flickering orange light, skin slick with sweat and orange reflections, watching a city burn aesthetic", "wind tunnel roar"),
    ("21_mountain", "Abstract golden mountain rising from a sea of dark teal storm clouds, volumetric lightning", "deep bass rumble"),
    ("22_apex_rise", "Soufflé top as a golden volcanic landscape, rising past the rim, high-texture aerated crumb, glistening", "crashing waves"),
    ("23_countdown", "Macro of digital display at 00:01, red glow blinding and bleeding into metal textures", "electric hum peaks"),
    ("24_glitch", "Visual glitch, image fracturing, colors inverting into neon purples and greens, digital artifacts, chromatic aberration", "glass shattering"),
    ("25_exhale", "Ultra-slow motion Arthur exhaling cold breath into warm amber air, thick swirling vapor clouds", "muffled underwater roar"),
    ("26_reveal", "Wall of golden light as oven door opens, engulfing the lens in bioluminescent haze, total lens flare", "white noise blast"),
    ("27_monument", "Extreme Macro of a still soufflé, monument of air and gold, crystalline sugar textures", "crystal clear ding"),
    ("28_blackout", "Solid black frame, total absence of light", "heavy sub-bass thud"),
    ("29_title", "Title Card THE ASCENT, gold foil text embossed on cracked black marble, high texture", "static crackle"),
    ("30_structure", "Text STRUCTURE FROM CHAOS, elegant silver typography in deep teal fog", "echoing whisper"),
    ("31_outnow", "Text OUT NOW, sharp metallic strike lighting up the letters", "sharp metallic strike"),
    ("32_spoon", "Final shot silver spoon breaking soufflé crust, steam erupting in amber light, man nodding in shadows", "deep hollow crunch"),
]

VO_SCRIPT = """
In the heart of the silence...
seconds become miles.
He made his choice.
There is no turning back.
The threshold...
is crossed.
An ocean in waiting.
He watches.
The energy shifts.
Time is a liquid.
Stretching.
Warping.
It is the ultimate test.
The first signs of defiance.
Will it break?
Or will it rise?
They said it was impossible.
To witness the transition...
from liquid...
to architecture.
The pressure...
is absolute.
Witness...
the apex.
OF!
THE ASCENT!
The Ascent.
Structure...
from chaos.
Coming Soon.
"""

def image_worker(proc_id, task_queue, args):
    os.environ["PYTORCH_ALLOC_CONF"] = "expandable_segments:True"
    model_id = args.model or DEFAULT_MODEL
    print(f"  [Process {proc_id}] Loading {model_id}...")
    try:
        pipe = StableDiffusion3Pipeline.from_pretrained(
            model_id, 
            torch_dtype=torch.float16 if DEVICE == "cuda" else torch.float32
        )
        if DEVICE == "cuda":
            pipe.enable_model_cpu_offload()
            pipe.vae.enable_tiling()
            pipe.vae.enable_slicing()
    except Exception as e:
        print(f"  [Process {proc_id}] Failed to load SD3.5: {e}")
        return

    while True:
        try:
            task = task_queue.get_nowait()
        except:
            break
        s_id, prompt_core = task
        out_path = f"{ASSETS_DIR}/images/{s_id}.png"
        full_prompt = prompt_core + PROMPT_SUFFIX
        print(f"  [Process {proc_id}] Generating: {s_id}")
        try:
            image = pipe(
                prompt=full_prompt,
                num_inference_steps=args.steps,
                guidance_scale=args.guidance,
                width=1024,
                height=1024,
            ).images[0]
            image = image.resize((1280, 720), Image.LANCZOS)
            image.save(out_path)
        except Exception as e:
            print(f"  [Process {proc_id}] Error generating {s_id}: {e}")
    del pipe; gc.collect()

def generate_images(args):
    print(f"--- Launching {args.num_procs} SD3.5 Processes for {len(SCENES)} Scenes ---")
    os.makedirs(f"{ASSETS_DIR}/images", exist_ok=True)
    to_generate = [(s_id, p) for s_id, p, _ in SCENES if not os.path.exists(f"{ASSETS_DIR}/images/{s_id}.png")]
    if not to_generate: return
    try: mp.set_start_method('spawn', force=True)
    except RuntimeError: pass
    task_queue = mp.Queue()
    for task in to_generate: task_queue.put(task)
    processes = [mp.Process(target=image_worker, args=(i, task_queue, args)) for i in range(args.num_procs)]
    for p in processes: p.start()
    for p in processes: p.join()

def generate_sfx(args):
    print(f"--- Generating High Quality SFX with Stable Audio Open ---")
    try:
        pipe = StableAudioPipeline.from_pretrained("stabilityai/stable-audio-open-1.0", torch_dtype=torch.float16 if DEVICE == "cuda" else torch.float32).to(DEVICE)
        os.makedirs(f"{ASSETS_DIR}/sfx", exist_ok=True)
        for s_id, _, sfx_core in SCENES:
            out_path = f"{ASSETS_DIR}/sfx/{s_id}.wav"
            if os.path.exists(out_path) and not utils.is_audio_bad(out_path): continue
            print(f"Generating SFX for: {s_id}")
            # Cyber-Noir SFX processing prompt
            sfx_prompt = f"High fidelity crisp cinematic foley, {sfx_core}, dark processed thriller sound, professional studio recording"
            for attempt in range(2):
                audio = pipe(sfx_prompt, num_inference_steps=200, audio_end_in_s=10.0).audios[0]
                wavfile.write(out_path, 44100, (audio.T.cpu().numpy() * 32767).astype(np.int16))
                if not utils.is_audio_bad(out_path): break
        del pipe
    except Exception as e: print(f"SFX generation failed: {e}")
    gc.collect()

def generate_voiceover(args):
    print("--- Generating High Quality Voiceover with F5-TTS ---")
    os.makedirs(f"{ASSETS_DIR}/voice", exist_ok=True)
    out_path_full = f"{ASSETS_DIR}/voice/voiceover_full.wav"
    if os.path.exists(out_path_full) and not utils.is_audio_bad(out_path_full): return
    lines = [l.strip() for l in VO_SCRIPT.split("\n") if l.strip()]
    temp_dir = f"{ASSETS_DIR}/voice/f5_temp"; os.makedirs(temp_dir, exist_ok=True)
    full_audio_data, sampling_rate = [], 44100
    for i, line in enumerate(lines):
        line_out_path = f"{ASSETS_DIR}/voice/vo_{i:03d}.wav"
        if os.path.exists(line_out_path) and not utils.is_audio_bad(line_out_path):
            sr, data = wavfile.read(line_out_path); full_audio_data.append(data); sampling_rate = sr; continue
        print(f"  Generating line {i}: {line[:30]}...")
        cmd = ["f5-tts_infer-cli", "--gen_text", line, "--output_dir", temp_dir]
        try:
            for f in os.listdir(temp_dir): os.remove(os.path.join(temp_dir, f))
            subprocess.run(cmd, check=True)
            gen = next((os.path.join(temp_dir, f) for f in os.listdir(temp_dir) if f.endswith(".wav")), None)
            if gen:
                os.replace(gen, line_out_path)
                sr, data = wavfile.read(line_out_path); full_audio_data.append(data); sampling_rate = sr
                full_audio_data.append(np.zeros(int(sr * 0.8), dtype=data.dtype))
        except Exception as e: print(f"  Line {i} failed: {e}")
    if full_audio_data: wavfile.write(out_path_full, sampling_rate, np.concatenate(full_audio_data))

def generate_music(args):
    print(f"--- Generating THE ASCENT Score with Stable Audio Open ---")
    os.makedirs(f"{ASSETS_DIR}/music", exist_ok=True)
    out_path = f"{ASSETS_DIR}/music/souffle_theme.wav"
    if os.path.exists(out_path) and not utils.is_audio_bad(out_path): return
    try:
        pipe = StableAudioPipeline.from_pretrained("stabilityai/stable-audio-open-1.0", torch_dtype=torch.float16 if DEVICE == "cuda" else torch.float32).to(DEVICE)
        # Multi-stage prompt based on souffle.md
        prompt = "30Hz Rezo sub-bass drone, dark cinematic atmospheric tension, building polyrythmic staccato strings, psychological thriller soundtrack, high fidelity"
        audio = pipe(prompt, num_inference_steps=200, audio_end_in_s=60.0).audios[0]
        wavfile.write(out_path, 44100, (audio.T.cpu().numpy() * 32767).astype(np.int16))
    except Exception as e: print(f"Music generation failed: {e}")
    gc.collect()

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--model", type=str, default=DEFAULT_MODEL)
    parser.add_argument("--steps", type=int, default=DEFAULT_STEPS)
    parser.add_argument("--guidance", type=float, default=DEFAULT_GUIDANCE)
    parser.add_argument("--num_procs", type=int, default=2)
    args = parser.parse_args()
    generate_images(args)
    generate_sfx(args)
    generate_voiceover(args)
    generate_music(args)
