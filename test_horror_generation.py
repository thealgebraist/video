import generate_horror_everyday
import os

# Override constants for testing
generate_horror_everyday.SCENES = [("test_scene", "A test horror scene", "scary sound")]
generate_horror_everyday.DEFAULT_STEPS = 1


class MockArgs:
    model = "hf-internal-testing/tiny-stable-diffusion-torch"
    steps = 1
    guidance = 0.0
    quant = "none"
    offload = True
    scalenorm = False


args = MockArgs()

print("Testing Image Generation...")
generate_horror_everyday.generate_images(args)
assert os.path.exists("assets_horror_everyday/images/test_scene.png")
print("Image Generation OK")

print("Testing SFX Generation...")
generate_horror_everyday.generate_sfx(args)
assert os.path.exists("assets_horror_everyday/sfx/test_scene.wav")
print("SFX Generation OK")

print("Testing Voiceover Generation...")
generate_horror_everyday.generate_voiceover(args)
assert os.path.exists("assets_horror_everyday/voice/voiceover_full.wav")
print("Voiceover Generation OK")

print("Testing Music Generation...")
generate_horror_everyday.generate_music(args)
assert os.path.exists("assets_horror_everyday/music/horror_theme.wav")
print("Music Generation OK")

print("All Tests Passed!")
