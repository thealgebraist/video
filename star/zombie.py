import torch
from diffusers import ZImagePipeline
import os

# 1. Load the pipeline
# Use bfloat16 for optimal performance on supported GPUs
device = "cuda" if torch.cuda.is_available() else "mps" if torch.backends.mps.is_available() else "cpu"
print(f"Using device: {device}")

# pipe = ZImagePipeline.from_pretrained(
#     "Tongyi-MAI/Z-Image-Turbo",
#     torch_dtype=torch.float32 if device == "cpu" else torch.bfloat16,
#     low_cpu_mem_usage=True,
# )
# pipe.to(device)

# # Load LoRA weights
# print("Loading LoRA: Technically-Color-Z-Image-Turbo...")
# pipe.load_lora_weights("renderartist/Technically-Color-Z-Image-Turbo")

# [Optional] Attention Backend
# Diffusers uses SDPA by default. Switch to Flash Attention for better efficiency if supported:

prompts = [
    "A confused zombie standing knee-deep in a small, stagnant puddle of rainwater on a city street, staring down at its own reflection, unable to comprehend the concept of stepping over the water.",
    "A group of zombies gathered at the edge of a backyard swimming pool, clawing at the air while a human floats on a raft just three feet away, safely separated by three feet of chlorinated water.",
    "A zombie trapped in a classic glass revolving door, walking endlessly in a circle as the door spins, never reaching the interior of the shopping mall.",
    "A medieval knight standing on a stone bridge over a narrow, three-foot-wide castle moat; below, dozens of zombies flail helplessly in the shallow water, unable to climb the slick vertical walls.",
    "A zombie attempting to walk up a down-moving escalator in a deserted airport, its legs moving in a slow, rhythmic shuffle that results in zero forward progress.",
    "A zombie whose foot is caught on a single strand of decorative holiday lights, causing it to hop comically in place while trying to reach a survivor just out of reach.",
    "A professional motorcyclist in full leather racing leathers and a reinforced helmet standing calmly as a zombie fruitlessly tries to bite through the tough, puncture-resistant hide.",
    "A zombie trapped in a child's ball pit at a fast-food restaurant, its flailing limbs only causing it to sink deeper into the sea of colorful plastic spheres.",
    "A line of zombies standing before a standard waist-high picket fence, reaching over it with their arms but failing to realize they could simply step over or push through the flimsy wood.",
    "A zombie stuck in a heavy mud flat after a rainstorm, its feet sunk six inches into the muck, pulling pathetically as it remains rooted to the spot.",
    "A survivor sitting comfortably on top of a standard kitchen refrigerator, looking down at a zombie that is unable to figure out how to climb a vertical surface with no handholds.",
    "A zombie trying to navigate a floor covered in thousands of loose marbles, its feet sliding out from under it with every attempt to move forward.",
    "A zombie trapped behind a simple screen door that opens outward; the zombie pushes against the mesh, only tightening the latch, unable to grasp the concept of pulling a handle.",
    "A lone zombie standing in front of a treadmill that is turned on to a slow walk, the zombie performing a perfect, unintended workout while staring blankly at the wall.",
    "A zombie attempting to climb a standard playground slide from the bottom, its rotting fingers sliding down the smooth plastic surface as it repeatedly falls back to the sand.",
    "A group of zombies defeated by a cattle grid on a country road, their legs falling through the gaps between the metal bars, leaving them pinned and dangling.",
    "A zombie getting its tattered shirt caught on a sturdy door handle, leading to it spinning in circles as it tries to move forward, effectively tethered to the door.",
    "A zombie failing to cross a small garden stream filled with decorative koi fish, the gentle six-inch flow of water acting as an impassable barrier to its primitive motor functions.",
    "A survivor standing on the opposite side of a standard airport security turnstile; the zombie pushes against the metal bar, which refuses to budge as it hasn't been 'activated'.",
    "A zombie attempting to bite a person wearing a 'shark suit' made of high-grade stainless steel chainmail, its teeth chipping and breaking against the metallic mesh.",
    "A zombie trapped in a large cardboard box that has been flipped upside down, the zombie bumping into the walls of its paper prison, unable to lift the edge to escape.",
    "A zombie trying to walk through a thick, manicured hedge in a suburban garden, its body becoming hopelessly entangled in the dense branches and leaves.",
    "A zombie standing on one side of a locked glass sliding door, licking the glass and scratching at its surface while the homeowner watches TV on the other side.",
    "A zombie defeated by a flight of stairs where the first step is slightly higher than usual, causing the zombie to trip and tumble back down in a heap.",
    "A group of zombies trapped in a cul-de-sac by a single row of parked shopping carts that have been chained together, forming a waist-high barricade.",
    "A zombie trying to bite through a thick, padded winter parka, its teeth merely sinking into the synthetic fluff without ever reaching the person's skin.",
    "A zombie attempting to cross a bridge made of thin nylon rope and wooden slats that sways violently in the wind, the zombie losing its balance and hanging by one arm.",
    "A zombie stuck in a hammock in a backyard, its limbs tangled in the rope mesh as it rolls back and forth, unable to find leverage to get out.",
    "A zombie failing to navigate a child's safety gate at the top of a staircase, rattling the plastic bars while a toddler watches from the other side.",
    "A zombie walking into a giant spider web in a dark forest, the sticky silk wrapping around its face and limbs, slowing its movement to a crawl.",
    "A zombie trying to climb a greased pole at a county fair, its hands sliding down the lubricated surface as it stares up at a prize it cannot reach.",
    "A zombie trapped in a walk-in freezer because it cannot figure out how to use the 'glow-in-the-dark' emergency release handle on the inside.",
    "A zombie attempting to walk through a car wash while the giant spinning brushes are active, the brushes pushing the zombie back and scrubbing its rotting skin.",
    "A zombie defeated by a simple latch on a garden gate that requires a thumb-press to open; the zombie claws at the wood but cannot perform the precise movement.",
    "A zombie stuck in a giant bubble wrap sheet spread across a warehouse floor, the popping sounds distracting it as it keeps falling over the slippery plastic.",
    "A zombie trying to walk up a steep, grassy hill that is wet with morning dew, sliding back down to the bottom with every three steps it takes.",
    "A zombie trapped in a clothing rack at a department store, its arms caught in the sleeves of various coats, making it look like a multi-armed monster.",
    "A zombie attempting to cross a field of wet, freshly poured concrete, its feet sinking and becoming encased in the hardening grey sludge.",
    "A zombie failing to get past a common household broom that has been wedged into the door frame, acting as a simple but effective bar.",
    "A zombie trying to bite a person through a thick, ornate medieval tapestry that has been thrown over it, the heavy fabric muffling its moans.",
    "A zombie stuck in a sandbox in a public park, its feet churning the loose sand but gaining no traction as it tries to reach a bench.",
    "A zombie falling into a trench that is only three feet deep, but because it cannot bend its knees properly, it remains trapped at the bottom, staring up.",
    "A zombie trying to walk through a bead curtain in a hippie-themed shop, the strings of beads wrapping around its neck and arms like tiny lassos.",
    "A zombie defeated by a revolving clothesline in a backyard; every time it lunges forward, the line spins, hitting it with wet laundry and pushing it away.",
    "A zombie trapped in a bounce house at a birthday party, its every step causing the floor to sink and rebound, sending the zombie flying into the inflatable walls.",
    "A zombie attempting to cross a floor covered in LEGO bricks, the sharp plastic edges causing it to stumble and fall, though it feels no pain.",
    "A zombie trying to climb a fire escape where the bottom ladder has been retracted, leaving it jumping pathetically for a rung that is ten feet in the air.",
    "A zombie stuck in a giant wind chime made of heavy bamboo pipes, the pipes clattering against its head as it tries to push through them.",
    "A zombie failing to open a child-proof cap on a bottle of medicine, despite banging the bottle against a rock for hours.",
    "A zombie trying to bite through a heavy-duty Kevlar vest worn by a tactical officer, its jaw muscles straining against the unbreakable fibers.",
    "A zombie trapped in a maze of mirrors at a carnival, repeatedly bumping into its own reflection and growling at the 'other' zombies.",
    "A zombie attempting to walk through a very thick, thorny rose bush, the thorns hooking into its flesh and holding it fast like a thousand tiny anchors.",
    "A zombie defeated by a common door stopper wedged firmly under a door, the zombie pushing with all its might while the door remains immovably ajar.",
    "A zombie trying to navigate a set of stepping stones in a koi pond, slipping on the mossy surface and falling face-first into the water.",
    "A zombie stuck in a giant fishing net that was draped over a pier, its flailing limbs only tightening the knots.",
    "A zombie attempting to climb a brick wall but failing because it lacks the finger strength to grip the mortar gaps.",
    "A zombie defeated by a standard office rolling chair; every time it tries to grab the chair for support, the chair rolls away, causing the zombie to fall.",
    "A zombie trapped in a phone booth, pushing against the glass door while the 'pull' handle remains untouched.",
    "A zombie trying to cross a bridge made of thin, flexible plastic sheeting that buckles under its weight, making the surface impossible to walk on.",
    "A zombie failing to get past a row of heavy velvet ropes at a movie theater, the weighted golden stands swaying but remaining upright.",
    "A zombie stuck in a deep pile of autumn leaves, its movements muffled and slowed as it disappears into the brown and orange foliage.",
    "A zombie trying to bite a man wearing a full suit of diving armor (atmospheric diving suit), the thick metal and glass carapace completely impenetrable.",
    "A zombie defeated by a slightly elevated threshold at the entrance of a shop, its dragging feet catching on the metal strip and sending it sprawling.",
    "A zombie standing in a heavy rainstorm, the downpour so thick that the zombie is blinded and simply stands still, waiting for the 'noise' to stop.",
]


os.makedirs("generations", exist_ok=True)


# Helper: produce a short, serious narration explaining how the obstacle defeats zombies
from pathlib import Path


def explain_defeat(prompt: str, index: int) -> str:
    p = prompt.lower()
    reason = None

    rules = [
        ("pool", "the standing water acts as an effective barrier; they will not swim and remain separated."),
        ("swimming pool", "chlorinated water keeps them at bay, preventing purposeful approach to the raft."),
        ("moat", "a slick vertical wall prevents ascent and keeps them from crossing."),
        ("revolving door", "endless circulation traps them in place, denying entry."),
        ("escalator", "the moving steps cancel any forward motion, leaving them stationary."),
        ("lights", "entangled decorative lights catch their feet and immobilize them."),
        ("helmet", "reinforced gear deflects their bites and makes attack futile."),
        ("ball pit", "an unstable, sinking surface swallows their steps and stops locomotion."),
        ("picket fence", "the simple fence blocks reach; they do not adapt by stepping over."),
        ("mud", "deep muck bogs them down until movement is impossible."),
        ("refrigerator", "a smooth, vertical surface leaves them unable to climb without handholds."),
        ("marbles", "treacherous footing from loose marbles undoes every attempt to move."),
        ("screen door", "the outward-opening latch requires a pull they never attempt."),
        ("treadmill", "the moving belt keeps them in place despite exertion."),
        ("slide", "the slick incline causes repeated slips and prevents ascent."),
        ("cattle grid", "gaps trap legs and pin them where they stand."),
        ("door handle", "a specific grasp-and-turn is required—something their motor plan lacks."),
        ("stream", "flowing water interrupts their gait and halts the approach."),
        ("turnstile", "an unactivated mechanism resists their push and stays locked."),
        ("chainmail", "tough material defeats their teeth; bites fail to penetrate."),
        ("cardboard box", "simple confinement leaves them trapped without the ability to escape."),
        ("hedge", "dense branches tangle limbs and hold them fast."),
        ("glass", "a transparent barrier they cannot bypass without tools or force."),
        ("stairs", "an irregular step disrupts balance and causes collapse."),
        ("shopping carts", "a chained barricade blocks passage effectively."),
        ("parka", "thick insulation absorbs bite attempts and prevents penetration."),
        ("rope", "an unstable, swaying walkway defeats their balance."),
        ("hammock", "the suspended fabric entangles and traps them in its weave."),
        ("safety gate", "a childproof latch denies passage to crude, repetitive motions."),
        ("web", "sticky silk gradually immobilizes contact points and slows progress."),
        ("greased", "a lubricated pole removes any effective grip and prevents climbing."),
        ("freezer", "cold interior conditions and an internal latch leave them trapped."),
        ("car wash", "mechanical brushes and water push them back and clear the approach."),
        ("bubble wrap", "a noisy, unstable surface and constant popping disrupt coordination."),
        ("lego", "sharp, uneven bricks create hazardous footing that prevents steady steps."),
        ("fire escape", "a missing lower rung leaves the ladder out of reach."),
        ("fishing net", "netting tightens with struggle and restrains limbs."),
        ("brick wall", "no handholds exist for climbing, so ascent fails."),
        ("rolling chair", "the chair moves away and removes necessary leverage."),
        ("phone booth", "an unexpected handle orientation prevents the required pull action."),
        ("velvet ropes", "low weighted barriers present an effective, unsurmountable boundary."),
        ("leaves", "loose, shifting material conceals and entraps, slowing movement."),
    ]

    for k, r in rules:
        if k in p:
            reason = r
            break

    # Return a concise reason sentence (no openers/closers)
    if reason is None:
        reason = ""

    return reason.capitalize()


# Helper: text-to-speech. Tries ElevenLabs (if API key and package present), otherwise falls back
# to gTTS (requires internet) and saves MP3. This keeps the code usable in many environments.
def tts_save(text: str, out_path: str, voice: str = "alloy"):
    """Save TTS as a WAV file at `out_path` without any further audio processing.

    This uses gTTS to create a temporary MP3 and immediately converts it to WAV.
    No pitch-shift or noise is applied.
    """
    out = Path(out_path)
    out.parent.mkdir(parents=True, exist_ok=True)

    # Prefer `vibevoice` if available. Try several common interfaces, then fall back to gTTS.
    # Try Coqui TTS (TTS package) first — high quality, free models.
    try:
        from TTS.api import TTS
        try:
            # This will download the model on first run if not present.
            tts = TTS(model_name="tts_models/en/vctk/vits")
            tts.tts_to_file(text=text or "", file_path=str(out))
            print(f"Saved TTS (Coqui TTS) to {out}")
            return
        except Exception as e:
            print(f"Coqui TTS synthesis failed: {e}")
    except Exception:
        # Coqui TTS not available
        pass

    try:
        import vibevoice

        try:
            # common simple API: synthesize(text, out_file, voice=...)
            if hasattr(vibevoice, "synthesize"):
                try:
                    vibevoice.synthesize(text=text or "", out_file=str(out), voice=voice)
                    print(f"Saved TTS (vibevoice.synthesize) to {out}")
                    return
                except TypeError:
                    # try alternate arg order
                    vibevoice.synthesize(str(out), text or "", voice=voice)
                    print(f"Saved TTS (vibevoice.synthesize alt) to {out}")
                    return

            # client style API
            if hasattr(vibevoice, "Client"):
                client = vibevoice.Client()
                if hasattr(client, "synthesize_to_file"):
                    client.synthesize_to_file(text or "", str(out), voice=voice)
                    print(f"Saved TTS (vibevoice.Client.synthesize_to_file) to {out}")
                    return
                if hasattr(client, "synthesize"):
                    client.synthesize(text=text or "", voice=voice, file=str(out))
                    print(f"Saved TTS (vibevoice.Client.synthesize) to {out}")
                    return

        except Exception as e:
            print(f"vibevoice present but synthesis failed: {e}")
            # fall through to fallback
    except Exception:
        # vibevoice not installed
        pass
    # Fallback: on macOS prefer the built-in `say` utility (high-quality voices),
    # convert the generated AIFF to WAV via ffmpeg.
    try:
        import platform
        import shutil
        import subprocess

        if platform.system() == "Darwin" and shutil.which("say"):
            if not (text and text.strip()):
                print("No text to speak (say)")
            else:
                tmp_aiff = str(out.with_suffix(".aiff"))
                # Use Alex or a deeper macOS voice if available
                voice_name = "Alex"
                try:
                    subprocess.run(["say", "-o", tmp_aiff, "-v", voice_name, text], check=True)
                    # convert AIFF -> WAV
                    subprocess.run(["/opt/homebrew/bin/ffmpeg", "-y", "-v", "warning", "-i", tmp_aiff, str(out)], check=True)
                    try:
                        os.remove(tmp_aiff)
                    except Exception:
                        pass
                    print(f"Saved TTS (macOS say) to {out}")
                    return
                except Exception as e:
                    print(f"macOS say synthesis failed: {e}")
    except Exception:
        pass

    # Fallback: gTTS -> mp3 -> convert to WAV via ffmpeg
    try:
        from gtts import gTTS
        import subprocess

        tmp_mp3 = str(out.with_suffix(".mp3"))
        t = gTTS(text=text or "", lang="en")
        t.save(tmp_mp3)
        # Convert MP3 -> WAV (no processing)
        cmd = ["/opt/homebrew/bin/ffmpeg", "-y", "-v", "warning", "-i", tmp_mp3, str(out)]
        subprocess.run(cmd, check=True)
        try:
            os.remove(tmp_mp3)
        except Exception:
            pass
        print(f"Saved TTS (gTTS) to {out}")
        return
    except Exception as e:
        print(f"TTS failed: {e}")
        return



def postprocess_audio(out_path: str, noise_level_db: int = -30):
    """No-op postprocessing kept for compatibility; does nothing.

    Audio processing has been disabled; audio files are saved as WAVs.
    """
    print("postprocess_audio: audio processing disabled; skipping.")

# 2. Generate Images
for i, prompt in enumerate(prompts):
    print(f"Generating image {i}/{len(prompts)}: {prompt[:50]}...")
    try:
        # image = pipe(
        #     prompt="t3chnic4lly, " + prompt,
        #     height=1024,
        #     width=1024,
        #     num_inference_steps=8,
        #     guidance_scale=0.0,
        #     generator=torch.Generator(device).manual_seed(42 + i),
        # ).images[0]
        
        # image.save(f"generations/zombies_{i:02d}.png")
        # Generate a short, serious narration for this image and save audio
        narration = explain_defeat(prompt, i)
        tts_out = f"generations/zombies_{i:02d}.wav"
        try:
            tts_save(narration, tts_out)
        except Exception as e:
            print(f"Failed to create TTS for image {i}: {e}")
    except Exception as e:
        print(f"Failed to generate image {i}: {e}")

print("Done! Check the 'generations' directory.")
