import os
import sys

sys.path.append(os.getcwd())

import generate_gollum_assets

# Override constants for testing
generate_gollum_assets.SCENES = [
    ("test_scene", "A test gollum developer scene", "scary sound")
]
generate_gollum_assets.VO_LINES = ["Test voiceover line."]
generate_gollum_assets.DEFAULT_STEPS = 1


class MockArgs:
    model = "hf-internal-testing/tiny-stable-diffusion-torch"  # Use tiny model for test
    steps = 1
    guidance = 0.0
    quant = "none"
    offload = True
    scalenorm = False


args = MockArgs()

print("Testing Image Generation...")
generate_gollum_assets.generate_images(args)
assert os.path.exists("assets_gollum_developer/images/test_scene.png")
print("Image Generation OK")

print("Testing SFX Generation...")
generate_gollum_assets.generate_sfx(args)
assert os.path.exists("assets_gollum_developer/sfx/test_scene.wav")
print("SFX Generation OK")

print("Testing Voiceover Generation...")
generate_gollum_assets.generate_voiceover(args)
assert os.path.exists("assets_gollum_developer/voice/voiceover_full.wav")
print("Voiceover Generation OK")

print("Testing Music Generation...")
generate_gollum_assets.generate_music(args)
assert os.path.exists("assets_gollum_developer/music/dev_descent.wav")
print("Music Generation OK")

print("All Tests Passed!")
