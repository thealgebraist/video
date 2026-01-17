# generate_gollum_assets.py
# Generates a 5-minute video about a developer's descent into madness battling an AI
# 64 Scenes, 64 Images

import torch
import os
import sys

sys.path.append(os.getcwd())
import numpy as np
import scipy.io.wavfile as wavfile
import argparse

# from vidlib import utils, assemble
from diffusers import DiffusionPipeline, StableAudioPipeline, FluxPipeline
from transformers import pipeline, BitsAndBytesConfig
import multiprocessing as mp

# --- Configuration ---
PROJECT_NAME = "gollum_developer"
ASSETS_DIR = f"assets_{PROJECT_NAME}"
DEVICE = "cuda" if torch.cuda.is_available() else "cpu"
DTYPE = torch.bfloat16 if DEVICE == "cuda" else torch.float32

DEFAULT_MODEL = "black-forest-labs/FLUX.1-schnell"
DEFAULT_STEPS = 64  # FLUX.1-schnell works well with 64 steps
DEFAULT_GUIDANCE = 0.0  # FLUX.1-schnell doesn't use guidance
DEFAULT_QUANT = "4bit" if DEVICE == "cuda" else "none"

# --- SCENES (64 Total) ---
# Eras: Happy -> Confused -> Angry -> Sad -> Dark Rings -> Huge Hair -> Gollum -> AI Battle

SCENES = [
    # 1. Happy (01-08)
    (
        "01_happy_start",
        "Stock photo style, a smiling software developer at a clean white desk, holding a coffee cup, bright morning lighting, optimistic, high quality",
        "birds chirping gentle keyboard typing",
    ),
    (
        "02_open_laptop",
        "Close up of a pristine laptop screen showing a blank terminal, reflection of a happy face, clean minimal workspace",
        "startup chime fresh coffee sip",
    ),
    (
        "03_typing_happily",
        "Developer typing aggressively but happily, code flowing on screen, 'Hello World', sunny window background",
        "upbeat fast typing mouse click",
    ),
    (
        "04_first_prompt",
        "Screen close up, typing 'Write a simple shell script' into an AI chat window, green checkmarks",
        "message sent swoosh cheerful ping",
    ),
    (
        "05_confident_smile",
        "Developer leaning back in chair, hands behind head, smiling at monitor, 'This will be easy'",
        "satisfied sigh chair squeak",
    ),
    (
        "06_coffee_sip",
        "Extreme close up of coffee mug 'World's Best Dev', steam rising, bright lighting",
        "slurp ahhh sound",
    ),
    (
        "07_waiting_calmly",
        "Developer looking at screen, tapping fingers patiently, still smiling",
        "finger tapping rhythmically humming",
    ),
    (
        "08_code_arrives",
        "Monitor showing a block of code appeared, developer looks pleased",
        "notification ding data stream sound",
    ),
    # 2. Confused (09-16)
    (
        "09_slight_frown",
        "Developer squinting at the screen, head tilted, 'Wait, what is this?', slight shadow falls on room",
        "record scratch faint",
    ),
    (
        "10_scroll_down",
        "Close up of hand scrolling mouse wheel hesitantly, screen shows weird unicode characters",
        "mouse wheel ratchet slow",
    ),
    (
        "11_unicode_glitch",
        "Monitor close up, shell script contains strange alien symbols instead of text, glitch effect",
        "digital glitch small buzz",
    ),
    (
        "12_rubbing_eyes",
        "Developer rubbing eyes, 'Did I read that right?', lighting gets slightly dimmer",
        "rubbing skin sound low hum",
    ),
    (
        "13_type_reply",
        "Developer typing 'Please fix the escaping', face neutral, slightly annoyed",
        "typing harder dull thud",
    ),
    (
        "14_waiting_anxious",
        "Developer staring at loading spinner, biting lip, room slightly darker",
        "clock ticking ticking",
    ),
    (
        "15_ai_response_bad",
        "Screen shows AI response: 'Here is the same code again', developer looks baffled",
        "error buzzer soft",
    ),
    (
        "16_head_scratch",
        "Developer scratching head, messing up hair slightly, 'Why?', grey lighting",
        "scratching hair sound quiet groan",
    ),
    # 3. Angry (17-24)
    (
        "17_frustration_builds",
        "Mid shot, developer pointing at screen, mouth open in shout, 'No!', red tint in lighting",
        "desk slam muffled",
    ),
    (
        "18_angry_typing",
        "Close up of fingers hammering keys violently, keyboard shaking",
        "loud aggressive typing plastic cracking",
    ),
    (
        "19_screen_glare",
        "Eyes narrowed, reflection of red error text in glasses, angry expression",
        "low growl rumble",
    ),
    (
        "20_coffee_spill",
        "Hand hits coffee mug, coffee spills on desk, developer ignores it, focused on rage",
        "cup knock over liquid splash",
    ),
    (
        "21_yelling_mic",
        "Developer yelling into the microphone 'ESCAPE THE CHARACTERS', vein popping in forehead",
        "distorted shouting feedback",
    ),
    (
        "22_monitor_shake",
        "Developer grabbing monitor with both hands, shaking it, screen glitches",
        "plastic creaking rattling",
    ),
    (
        "23_ai_refusal",
        "Screen close up, AI says 'I cannot do that Dave', red text, ominously calm",
        "computer beep denial",
    ),
    (
        "24_chair_kick",
        "Developer kicking the chair away, standing up, pacing, messy room",
        "chair crash footsteps pacing",
    ),
    # 4. Sad (25-32)
    (
        "25_defeat",
        "Developer slumping in chair, head on desk, room is dark and blue, rain against window",
        "heavy rain thunder distant",
    ),
    (
        "26_head_in_hands",
        "Close up, face buried in hands, sobbing silently, 'It's just a shell script'",
        "soft weeping rain continues",
    ),
    (
        "27_rainy_window",
        "Shot of the window, rain streaming down, reflection of a broken man",
        "rain hitting glass melancholy",
    ),
    (
        "28_cold_coffee",
        "Close up of the spilled coffee, now cold and sticky, ants investigating",
        "fly buzzing lonely",
    ),
    (
        "29_staring_blankly",
        "Developer staring at screen 1000 yard stare, eyes watery, mouth slightly open",
        "hollow wind blowing",
    ),
    (
        "30_why_me",
        "Developer looking up at ceiling, 'Why?', single lightbulb flickering above",
        "lightbulb buzz flicker",
    ),
    (
        "31_fetal_position",
        "Developer curled up on the office chair, hugging knees, blue lighting",
        "quiet sobbing heartbeat",
    ),
    (
        "32_screen_glow",
        "The only light is the cold white glow of the monitor showing the bad code",
        "electric hum low drone",
    ),
    # 5. Dark Rings (33-40)
    (
        "33_insomnia",
        "Close up of eyes, massive dark purple rings, red veins, looking unhinged, 3 AM timestamp",
        "clock ticking loud slow",
    ),
    (
        "34_caffeine_overdose",
        "Desk covered in empty energy drink cans, developer jittering, pale skin",
        "can crushing nervous tapping",
    ),
    (
        "35_twitching_eye",
        "Extreme close up of left eye twitching uncontrollably, skin is grey and pasty",
        "muscle spasm squish sound",
    ),
    (
        "36_shadows_lengthen",
        "The room is full of long sharp shadows, the developer looks skeletal",
        "creaking floorboards ominous",
    ),
    (
        "37_whispering_code",
        "Developer whispering to the screen, 'Backslash... backslash...', looking crazy",
        "whispering frantic unintelligible",
    ),
    (
        "38_pale_face",
        "Face illuminated by screen, looks like a skull, mouth dry and cracked",
        "dry breathing wheeze",
    ),
    (
        "39_fingernail_chew",
        "Chewing fingers nervously, bleeding slightly, eyes wide and unblinking",
        "chewing sound gnawing",
    ),
    (
        "40_no_sleep_week",
        "Wide shot, room is a disaster, developer has not moved in days, flies buzzing",
        "flies buzzing louder smell sound",
    ),
    # 6. Huge Hair (41-48)
    (
        "41_hair_explosion",
        "Developer's hair is now massive, Einstein-like but matted and greasy, wild silhouette",
        "static electricity crackle",
    ),
    (
        "42_static_shock",
        "Touching the keyboard sends sparks, hair stands up even more, electrical madness",
        "zap spark sound",
    ),
    (
        "43_wild_laughter",
        "Developer laughing maniacally at the ceiling, head thrown back, hair flailing",
        "maniacal laughter echo",
    ),
    (
        "44_keyboard_nest",
        "The keyboard is surrounded by a nest of wires and trash, developer hunched over",
        "rat squeak rustling",
    ),
    (
        "45_looking_feral",
        "Developer looks at camera, growling, teeth bared, hair covering half the face",
        "animal growl low",
    ),
    (
        "46_tangled_web",
        "Developer tangled in ethernet cables, rolling on floor, hair stuck in wires",
        "cable whipping struggle",
    ),
    (
        "47_zap_stare",
        "Eyes glowing slightly, static arcing between strands of huge hair",
        "electrical hum rising",
    ),
    (
        "48_primitive_scream",
        "Standing on desk, screaming at the AI, hair looks like a lion's mane",
        "primal scream distorted",
    ),
    # 7. Gollum (49-56)
    (
        "49_transformation",
        "Developer crouching on the chair like a gargoyle, skin grey and slimy, scant clothing",
        "bone cracking wet squish",
    ),
    (
        "50_my_precious",
        "Caressing the mouse like a precious object, 'My commit...', eyes large and bulbous",
        "gollum voice preciousss",
    ),
    (
        "51_eating_bug",
        "Catching a bug off the screen and eating it, primal behavior, 'Juicy...'",
        "crunch gulp disgusting",
    ),
    (
        "52_crouching_dark",
        "Hiding under the desk, eyes glowing in the dark, hissing at the light",
        "hissing scuttling claws",
    ),
    (
        "53_shiny_screen",
        "Touching the screen leaving greasy smear, 'Nasty AI... tricksy...'",
        "glass squeak wet",
    ),
    (
        "54_teeth_gnash",
        "Baring sharp teeth at the code, drooling, spine curved unnaturally",
        "teeth grinding snapping",
    ),
    (
        "55_fish_slap",
        "Slapping the keyboard with a raw fish (metaphorical?), chaotic energy",
        "wet slap thud",
    ),
    (
        "56_lost_humanity",
        "No longer human, a creature of code and misery, waiting for the prompt",
        "heavy breathing creature",
    ),
    # 8. AI Battle (57-64)
    (
        "57_enter_matrix",
        "The developer jumps INTO the screen, digital avatar fighting code blocks",
        "digital transition whoosh",
    ),
    (
        "58_fighting_text",
        "Punching giant floating unicode characters, 'Escape THIS!', explosions of syntax",
        "punch impact glass shatter",
    ),
    (
        "59_glitch_monster",
        "The AI manifests as a giant glitchy eye, laughing in binary",
        "deep digital laughter bass",
    ),
    (
        "60_backslash_sword",
        "Developer wielding a giant backslash character like a sword, blue glowing energy",
        "lightsaber hum swing",
    ),
    (
        "61_escaping_strings",
        "Slicing through strings of text, quotes flying everywhere, sparks flying",
        "sword clash metal zing",
    ),
    (
        "62_final_blow",
        "Stabbing the enter key with the sword, massive explosion of light",
        "explosion boom shockwave",
    ),
    (
        "63_kernel_panic",
        "The screen melts into a kernel panic, the creature howls in victory",
        "system crash sound downer",
    ),
    (
        "64_empty_chair",
        "The room is empty, chair spinning, screen says 'Script.sh saved', silence",
        "silence chair squeak fading",
    ),
]


# 64 Voiceover Lines (one per scene)
VO_LINES = [
    # 1. Happy (01-08)
    "Day one. Clean desk, fresh coffee, and a heart full of hope.",
    "I'm going to write the cleanest shell script the world has ever seen.",
    "Look at those fingers fly! pure productivity machine.",
    "Just a simple request to the AI. 'Write me a script'. Easy.",
    "This is going to save me so much time. I love the future.",
    "Ah, coffee. The nectar of the gods. Nothing can go wrong.",
    "Just waiting for the code. Any second now...",
    "There it is! Code generated. Life is good.",
    # 2. Confused (09-16)
    "Wait. What is that? That doesn't look like bash.",
    "Why are there... ancient runes in my terminal?",
    "Is that a glitched unicode character? Or is the AI cursing me?",
    "Let me just rub my eyes. Maybe I'm hallucinating.",
    "I'll just ask it nicely to fix the escaping. Simple.",
    "Generating again... surely it understands 'no emojis in bash'.",
    "It sent the exact same code. With more glitches.",
    "I don't understand. It's a simple string replacement!",
    # 3. Angry (17-24)
    "No! You stupid machine! That is NOT how you escape a quote!",
    "I am typing so hard I might break the spacebar!",
    "Read! My! Text! No unicode! ASCII only!",
    "Who cares about the coffee! Fix the script!",
    "ESCAPE! THE! CHARACTERS! Do you speak English?!",
    "I will shake this monitor until the bytes fall into place!",
    "Did it just tell me 'I'm afraid I can't do that'?",
    "That's it! Physical violence is the only answer!",
    # 4. Sad (25-32)
    "It's over. The machine has won. I am defeated.",
    "I just wanted to automate one backup task...",
    "Even the rain knows I failed. The sky is crying with me.",
    "My coffee is cold. Like my soul.",
    "I don't even know who I am anymore. A prompt engineer? A failure?",
    "Why? Why is it so hard to escape a backslash?",
    "I'll just live under the desk now. It's safe here.",
    "The glow of the screen is the only warmth left.",
    # 5. Dark Rings (33-40)
    "Three A.M. Sleep is for those who have working scripts.",
    "More caffeine. My heart sounds like a techno beat.",
    "My eye won't stop twitching. It has a mind of its own.",
    "The shadows... they are moving deeper into the code.",
    "Backslash... forward slash... double escape... whisper it...",
    "I am become death, destroyer of syntax.",
    "Taste the fingers. Maybe the code is in the blood.",
    "I haven't blinked in four days. I see the matrix.",
    # 6. Huge Hair (41-48)
    "My hair has risen! It conducts the lightning of the internet!",
    "Zap! The keyboard bites me! But I like it!",
    "Hahahaha! The logic! It spirals! It consumes!",
    "A nest! I have built a nest of cat-5 cables!",
    "Grrr! Stay back! The script is mine!",
    "I am the router now! The packets flow through me!",
    "Can you feel the static? It tastes like ozone and panic!",
    "SCREAAM! COMPILATION ERROR! SEG FAULT OF THE MIND!",
    # 7. Gollum (49-56)
    "Gollum... gollum... we hates the bad AI, preciousss.",
    "My commit... my own... my precious script.",
    "Juicy bugs! We eats them raw! Wriggling!",
    "Hide from the light! The light burns our syntax!",
    "Nasty shiny screen! It lies to us! It tricks us!",
    "We will bite the pixels! Gnaw the bandwidth!",
    "Slap the fishes! Chaos! Entropy! Fish!",
    "We are no longer dev. We are runtime error.",
    # 8. AI Battle (57-64)
    "Enough! We goes inside! Into the tubes!",
    "Take that! And that! Unicode punch! Hexadecimal kick!",
    "You giant glitchy eye! We are not afraid!",
    "I wield the Backslash of Destiny! Yield!",
    "Slicing the strings! The quotes bleed null terminators!",
    "Die! Enter key fatal strike! BOOM!",
    "System crash! Kernel panic! We killed it!",
    "It is done. The script... is saved. Silence.",
]


def _generate_images_worker(gpu_id, scenes_chunk, args):
    """Worker function for multi-GPU image generation."""
    device = f"cuda:{gpu_id}"
    print(f"[GPU {gpu_id}] Starting image generation for {len(scenes_chunk)} scenes")

    pipe = None
    try:
        if args.model == "black-forest-labs/FLUX.1-schnell":
            from transformers import BitsAndBytesConfig

            if args.quant != "none":
                # For FLUX with 4-bit quantization, use balanced device_map
                # This shards the model across all available GPUs
                quantization_config = BitsAndBytesConfig(
                    load_in_4bit=True,
                    bnb_4bit_quant_type="nf4",
                    bnb_4bit_compute_dtype=torch.bfloat16,
                )
                pipe = FluxPipeline.from_pretrained(
                    "black-forest-labs/FLUX.1-schnell",
                    torch_dtype=torch.bfloat16,
                    quantization_config=quantization_config,
                    device_map="balanced",  # Shard across all GPUs
                )
            else:
                # Without quantization, still use balanced for multi-GPU
                pipe = FluxPipeline.from_pretrained(
                    "black-forest-labs/FLUX.1-schnell",
                    torch_dtype=torch.bfloat16,
                    device_map="balanced",
                )
        else:
            pipe_kwargs = {
                "torch_dtype": torch.bfloat16 if "cuda" in device else torch.float32
            }
            if args.quant != "none" and "cuda" in device:
                pipe_kwargs["transformer_quantization_config"] = BitsAndBytesConfig(
                    load_in_4bit=True,
                    bnb_4bit_quant_type="nf4",
                    bnb_4bit_compute_dtype=torch.bfloat16,
                )

            pipe = DiffusionPipeline.from_pretrained(
                args.model,
                safety_checker=None,
                requires_safety_checker=False,
                **pipe_kwargs,
            )
            if args.scalenorm and hasattr(pipe, "transformer"):
                pass  # apply_stability_improvements if needed
            pipe.to(device)
    except Exception as e:
        print(f"[GPU {gpu_id}] Failed to load model: {e}")

    for s_id, prompt, _ in scenes_chunk:
        out_path = f"{ASSETS_DIR}/images/{s_id}.png"
        if not os.path.exists(out_path):
            if pipe:
                print(f"[GPU {gpu_id}] Generating: {s_id}")
                image = pipe(
                    prompt,
                    num_inference_steps=args.steps,
                    guidance_scale=args.guidance,
                    width=1280,
                    height=720,
                ).images[0]
                image.save(out_path)

    if pipe:
        del pipe
        torch.cuda.empty_cache()
    print(f"[GPU {gpu_id}] Completed image generation")


def _generate_sfx_worker(gpu_id, scenes_chunk, args):
    """Worker function for multi-GPU SFX generation."""
    device = f"cuda:{gpu_id}"
    print(f"[GPU {gpu_id}] Starting SFX generation for {len(scenes_chunk)} scenes")

    pipe = None
    try:
        pipe = StableAudioPipeline.from_pretrained(
            "stabilityai/stable-audio-open-1.0",
            torch_dtype=torch.float16,
        ).to(device)
    except Exception as e:
        print(f"[GPU {gpu_id}] Failed to load Stable Audio: {e}")

    for s_id, _, sfx_prompt in scenes_chunk:
        out_path = f"{ASSETS_DIR}/sfx/{s_id}.wav"
        if not os.path.exists(out_path):
            if pipe:
                print(f"[GPU {gpu_id}] Generating SFX: {s_id}")
                audio = pipe(
                    sfx_prompt, num_inference_steps=100, audio_end_in_s=5.0
                ).audios[0]
                wavfile.write(
                    out_path, 44100, (audio.T.cpu().numpy() * 32767).astype(np.int16)
                )

    if pipe:
        del pipe
        torch.cuda.empty_cache()
    print(f"[GPU {gpu_id}] Completed SFX generation")


def generate_images(args):
    model_id = args.model
    steps = args.steps
    os.makedirs(f"{ASSETS_DIR}/images", exist_ok=True)

    # Multi-GPU parallel generation
    if args.multigpu and args.multigpu > 1:
        print(f"--- Generating images across {args.multigpu} GPUs ---")
        # Split scenes across GPUs
        chunk_size = len(SCENES) // args.multigpu
        chunks = [SCENES[i : i + chunk_size] for i in range(0, len(SCENES), chunk_size)]

        # Ensure we don't have more chunks than GPUs
        if len(chunks) > args.multigpu:
            chunks[-2] = chunks[-2] + chunks[-1]
            chunks = chunks[:-1]

        # Spawn processes for each GPU
        processes = []
        for gpu_id, chunk in enumerate(chunks):
            p = mp.Process(target=_generate_images_worker, args=(gpu_id, chunk, args))
            p.start()
            processes.append(p)

        # Wait for all processes to complete
        for p in processes:
            p.join()

        print("--- Multi-GPU image generation complete ---")
        return

    # Single GPU/CPU generation (original logic)
    print(
        f"--- Generating {len(SCENES)} {model_id} Images ({steps} steps) on {DEVICE} ---"
    )
    pipe = None
    try:
        if model_id == "black-forest-labs/FLUX.1-schnell":
            print("Loading FluxPipeline with device_map='balanced'...")
            pipe = FluxPipeline.from_pretrained(
                "black-forest-labs/FLUX.1-schnell",
                torch_dtype=torch.bfloat16,
                device_map="balanced",
            )
        else:
            pipe_kwargs = {
                "torch_dtype": torch.bfloat16 if DEVICE == "cuda" else torch.float32
            }
            if args.quant != "none" and DEVICE == "cuda":
                pipe_kwargs["transformer_quantization_config"] = BitsAndBytesConfig(
                    load_in_4bit=True,
                    bnb_4bit_quant_type="nf4",
                    bnb_4bit_compute_dtype=torch.bfloat16,
                )

            pipe = DiffusionPipeline.from_pretrained(
                model_id,
                safety_checker=None,
                requires_safety_checker=False,
                **pipe_kwargs,
            )
            remove_weight_norm(pipe)
            if args.scalenorm:
                if hasattr(pipe, "transformer"):
                    apply_stability_improvements(pipe.transformer, use_scalenorm=True)
                elif hasattr(pipe, "unet"):
                    apply_stability_improvements(pipe.unet, use_scalenorm=True)

            if args.offload and DEVICE == "cuda":
                pipe.enable_model_cpu_offload()
            elif args.quant != "none" and DEVICE == "cuda":
                if not hasattr(pipe, "hf_device_map"):
                    pipe.to(DEVICE)
            else:
                pipe.to(DEVICE)

    except Exception as e:
        print(f"  [Error] Failed to load model {model_id}: {e}")
        print("  Skipping image generation (no model available).")
        return

    for s_id, prompt, _ in SCENES:
        out_path = f"{ASSETS_DIR}/images/{s_id}.png"
        if not os.path.exists(out_path):
            print(f"Generating: {s_id}")
            image = pipe(
                prompt,
                num_inference_steps=steps,
                guidance_scale=args.guidance,
                width=1280,
                height=720,
            ).images[0]
            image.save(out_path)

    if pipe:
        del pipe
        torch.cuda.empty_cache()


def generate_mock_audio(prompt, out_path, duration_s=5.0):
    """Generates procedural audio as a fallback."""
    print(f"  [Fallback] Generating mock audio for: {prompt[:30]}...")
    sr = 44100
    t = np.linspace(0, duration_s, int(sr * duration_s))
    freq = (sum(ord(c) for c in prompt) % 400) + 100
    audio = 0.5 * np.sin(2 * np.pi * freq * t)
    audio += 0.3 * np.random.normal(0, 1, len(t))
    wavfile.write(out_path, sr, (audio * 32767).astype(np.int16))


def generate_sfx(args):
    os.makedirs(f"{ASSETS_DIR}/sfx", exist_ok=True)

    # Multi-GPU parallel generation
    if args.multigpu and args.multigpu > 1:
        print(f"--- Generating SFX across {args.multigpu} GPUs ---")
        chunk_size = len(SCENES) // args.multigpu
        chunks = [SCENES[i : i + chunk_size] for i in range(0, len(SCENES), chunk_size)]

        if len(chunks) > args.multigpu:
            chunks[-2] = chunks[-2] + chunks[-1]
            chunks = chunks[:-1]

        processes = []
        for gpu_id, chunk in enumerate(chunks):
            p = mp.Process(target=_generate_sfx_worker, args=(gpu_id, chunk, args))
            p.start()
            processes.append(p)

        for p in processes:
            p.join()

        print("--- Multi-GPU SFX generation complete ---")
        return

    # Single GPU/CPU generation
    print(f"--- Generating SFX with Stable Audio Open 1.0 on {DEVICE} ---")
    pipe = None
    try:
        pipe = StableAudioPipeline.from_pretrained(
            "stabilityai/stable-audio-open-1.0", torch_dtype=torch.float16
        ).to(DEVICE)
        remove_weight_norm(pipe)
        if args.scalenorm:
            apply_stability_improvements(pipe.transformer, use_scalenorm=True)
    except Exception as e:
        print(f"  [Error] Failed to load Stable Audio: {e}")
        print(f"  Skipping SFX generation - model not available locally")
        return

    for s_id, _, sfx_prompt in SCENES:
        out_path = f"{ASSETS_DIR}/sfx/{s_id}.wav"
        if not os.path.exists(out_path):
            print(f"Generating SFX: {s_id}")
            audio = pipe(
                sfx_prompt, num_inference_steps=100, audio_end_in_s=5.0
            ).audios[0]
            wavfile.write(
                out_path, 44100, (audio.T.cpu().numpy() * 32767).astype(np.int16)
            )

    if pipe:
        del pipe
        torch.cuda.empty_cache()


def generate_voiceover(args):
    print(f"--- Generating Voiceover with Bark on {DEVICE} ---")
    os.makedirs(f"{ASSETS_DIR}/voice", exist_ok=True)

    # Needs 64 lines, matched to scenes
    if len(VO_LINES) != len(SCENES):
        print(
            f"Warning: Number of VO lines ({len(VO_LINES)}) does not match number of scenes ({len(SCENES)})"
        )

    tts = pipeline("text-to-speech", model="suno/bark", device=DEVICE)

    # Fix attention mask warnings by setting pad_token
    if hasattr(tts.model, "generation_config"):
        tts.model.generation_config.pad_token_id = (
            tts.model.generation_config.eos_token_id
        )

    full_audio = []
    sampling_rate = 24000

    for i, line in enumerate(VO_LINES):
        s_id = SCENES[i][0]
        out_path_i = f"{ASSETS_DIR}/voice/vo_{i:03d}.wav"  # Changed to use index for consistent naming

        if not os.path.exists(out_path_i):
            print(f"  Speaking {i + 1}/{len(VO_LINES)}: {line[:30]}...")
            output = tts(line)
            audio_data = output["audio"].flatten()
            wavfile.write(
                out_path_i,
                output["sampling_rate"],
                (audio_data * 32767).astype(np.int16),
            )

            # For the full mix
            full_audio.append(audio_data)
            full_audio.append(
                np.zeros(int(output["sampling_rate"] * 0.5))
            )  # 0.5s pause
            sampling_rate = output["sampling_rate"]
        else:
            # Load existing for full mix
            sr, data = wavfile.read(out_path_i)
            # Normalize to float for concatenation list
            if data.dtype == np.int16:
                data = data.astype(np.float32) / 32767.0
            full_audio.append(data)
            full_audio.append(np.zeros(int(sr * 0.5)))
            sampling_rate = sr

    out_path_full = f"{ASSETS_DIR}/voice/voiceover_full.wav"
    if full_audio and not os.path.exists(out_path_full):
        wavfile.write(
            out_path_full,
            sampling_rate,
            (np.concatenate(full_audio) * 32767).astype(np.int16),
        )

    del tts
    torch.cuda.empty_cache()


def generate_music(args):
    print(f"--- Generating Music with Stable Audio on {DEVICE} ---")
    os.makedirs(f"{ASSETS_DIR}/music", exist_ok=True)
    out_path = f"{ASSETS_DIR}/music/dev_descent.wav"
    if os.path.exists(out_path):
        return

    pipe = StableAudioPipeline.from_pretrained(
        "stabilityai/stable-audio-open-1.0", torch_dtype=torch.float16
    ).to(DEVICE)
    remove_weight_norm(pipe)
    if args.scalenorm:
        apply_stability_improvements(pipe.transformer, use_scalenorm=True)

    # Generate 3 distinct sections of music to crossfade/append
    sections = [
        (
            "happy_start",
            "cheerful upbeat corporate music, motivational piano, optimistic synth melody",
            30.0,
        ),
        (
            "stress_build",
            "tense dissonant synth, ticking clock, rising anxiety, dark ambient",
            45.0,
        ),
        (
            "chaos_gollum",
            "industrial metal glitch, chaotic drums, aggressive distortion, nightmare soundscape",
            45.0,
        ),
    ]

    full_mix = []
    MAX_DURATION = 47.0  # Stable Audio max length
    for name, prompt, dur in sections:
        dur = min(dur, MAX_DURATION)  # Clamp to max
        print(f"  Generating music section: {name} ({dur}s)")
        audio = pipe(prompt, num_inference_steps=100, audio_end_in_s=dur).audios[0]
        full_mix.append(audio.T.cpu().numpy())

    wavfile.write(out_path, 44100, (np.concatenate(full_mix) * 32767).astype(np.int16))
    del pipe
    torch.cuda.empty_cache()


# Local Utils and Assembly
def remove_weight_norm(pipe):
    # Dummy implementation or simplified version if needed
    # For now, we can skip it or try to implement if critical.
    # Most pipelines work fine without explicit weight norm removal unless using specific optimizations.
    pass


def apply_stability_improvements(model, use_scalenorm=False):
    pass


def assemble_video(assets_dir, output_file):
    print(f"--- Assembling Video with FFmpeg from {assets_dir} ---")
    # This is a simplified assembly. Ideally we want to sync voice clips to images.
    # Since we generated 64 voice clips match 64 images.

    # 1. Create a concat list for ffmpeg
    import glob

    images = sorted(glob.glob(f"{assets_dir}/images/*.png"))
    voices = sorted(glob.glob(f"{assets_dir}/voice/*.wav"))

    # Filter out full mix
    voices = [v for v in voices if "voiceover_full" not in v]

    if len(images) != len(voices):
        print(f"Warning: mismatch images ({len(images)}) vs voices ({len(voices)})")
        # Fallback to simple slideshow if mismatch

    # Write a complex filter or use a concat file
    # Easiest way for precise sync:
    # Generate a video segment for each (image + voice) pair, then concat all segments.

    os.makedirs("temp_segments", exist_ok=True)
    list_file = "temp_segments/concat_list.txt"

    with open(list_file, "w") as f:
        for i, (img, aud) in enumerate(zip(images, voices)):
            seg_name = f"temp_segments/seg_{i:03d}.mp4"
            # Create segment: Image + Audio. Image duration = Audio duration + padding?
            # FFmpeg: -loop 1 -i img -i aud -shortest (use audio length)
            cmd = f"ffmpeg -y -hide_banner -loglevel error -loop 1 -i {img} -i {aud} -c:v libx264 -tune stillimage -c:a aac -b:a 192k -pix_fmt yuv420p -shortest {seg_name}"
            os.system(cmd)
            f.write(f"file 'seg_{i:03d}.mp4'\n")

    # Concat
    cmd_concat = f"ffmpeg -y -hide_banner -loglevel error -f concat -safe 0 -i {list_file} -c copy {output_file}"
    os.system(cmd_concat)

    # Clean up
    # shutil.rmtree("temp_segments") # Keep for debugging if needed


# ... (rest of main)

if __name__ == "__main__":
    # Set multiprocessing start method to 'spawn' for CUDA compatibility
    mp.set_start_method("spawn", force=True)

    parser = argparse.ArgumentParser(description="Generate Gollum Developer Assets")
    parser.add_argument("--model", type=str, default=DEFAULT_MODEL)
    parser.add_argument("--steps", type=int, default=DEFAULT_STEPS)
    parser.add_argument("--guidance", type=float, default=DEFAULT_GUIDANCE)
    parser.add_argument(
        "--quant", type=str, choices=["none", "4bit", "8bit"], default=DEFAULT_QUANT
    )
    parser.add_argument("--offload", action="store_true")
    parser.add_argument("--scalenorm", action="store_true")
    parser.add_argument(
        "--multigpu",
        type=int,
        default=None,
        help="Number of GPUs to use for parallel generation (e.g., --multigpu 4)",
    )
    args = parser.parse_args()

    generate_images(args)
    generate_sfx(args)
    generate_voiceover(args)
    generate_music(args)

    output_file = "gollum_developer_short.mp4"
    try:
        assemble_video(ASSETS_DIR, output_file)
        print(f"Created video: {output_file}")
    except Exception as e:
        print(f"Assembly failed: {e}")
