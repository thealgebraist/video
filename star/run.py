import torch
from diffusers import ZImagePipeline
import os

# 1. Load the pipeline
# Use bfloat16 for optimal performance on supported GPUs
device = "cuda" if torch.cuda.is_available() else "mps" if torch.backends.mps.is_available() else "cpu"
print(f"Using device: {device}")

pipe = ZImagePipeline.from_pretrained(
    "Tongyi-MAI/Z-Image-Turbo",
    torch_dtype=torch.float32 if device == "cpu" else torch.bfloat16,
    low_cpu_mem_usage=True,
)
pipe.to(device)

# [Optional] Attention Backend
# Diffusers uses SDPA by default. Switch to Flash Attention for better efficiency if supported:
# if device == "cuda":
#     pipe.transformer.set_attention_backend("flash")

prompts = [
    "Darth Vader helmet fused with a human skull, obsidian chitinous bone, weeping sores at eye sockets, pulsating esophageal breathing tubes, body horror Star Wars.",
    "Stormtrooper armor made of calcified bone and stretched tendons, joints leaking synovial fluid, retinal tissue visor with multiple tiny eyes inside, flesh horror.",
    "Millennium Falcon as a planetary scavenger organism, hull of hardened gray flesh and barnacle scales, cockpit is a giant glassy eye, bioluminescent green slime engines.",
    "Chewbacca covered in millions of writhing parasitic hair-worms, mouth as a vertical slit with needle-teeth, dripping black bile, body horror wookiee.",
    "Princess Leia in slave outfit with living twitching umbilical cord chains, eyes replaced with black voids, translucent skin dress, grotesque beauty.",
    "Lightsaber handle made of a preserved human humerus bone, blade is a beam of concentrated glowing necrotic plasma sizzling the air.",
    "C-3PO made of polished golden cartilage and raw muscle fibers, exposed nervous system wires sparking yellow bioluminescence, wet human eyeballs.",
    "R2-D2 as a cylindrical biomechanical cyst, covered in pulsing veins and dripping oily lymph, weeping optic lens with muscular spasms.",
    "Yoda as a multi-limbed creature of ancient mossy flesh, translucent skin showing glowing capillaries, sitting on a throne of spinal cords.",
    "Boba Fett jetpack made of auxiliary lungs and blood sacs, armor of flayed leather and bone plates, helmet fused to raw neck tissue.",
    "TIE Fighter wings as vast leathery membranes stretched over skeletal fingers, central pod is a throbbing muscular heart in a crystal sphere.",
    "X-Wing fuselage made of rib-cages and lungs, s-foils are iridescent insectoid wings dripping ichor, astromech is a brain in a jar.",
    "Jabba the Hutt as an undulating mountain of gelatinous fat, millions of tiny screaming human faces embedded in his slime-coated body.",
    "Darth Maul with horns that are actually protruding nerve bundles, skin a map of flayed muscular tattoos, double-bladed spine lightsaber.",
    "The Emperor Palpatine as a lich with sloughing skin, core of crackling dark energy, robes made of shadow and dried entrails.",
    "General Grievous as a construct of alien limbs stitched with high-tensile tendons, four arms holding light-spines of concentrated agony.",
    "AT-AT walker as a colossus of gray flesh and bone, legs are multi-jointed chitinous limbs, head is a skull-like cockpit weeping oil.",
    "Han Solo frozen in carbonite, but the carbonite is semi-translucent necrotic flesh, his body partially digested and merged with the block.",
    "Obi-Wan Kenobi ghost as a shimmering, translucent entity of exposed organs and blue spectral energy, radiating a cold sense of dread.",
    "Ewok as a small, feral creature of matted fur and multiple weeping eyes, teeth made of sharpened infant bone, wearing a scalp as a cowl.",
    "Sand People (Tusken Raiders) with masks made of sun-dried facial skin, respirators fused into their throats, holding staves of spinal bone.",
    "The Death Star as a planetary-scale ocular organ, a giant bloodshot eyeball in space, the superlaser iris firing a beam of concentrated fire.",
    "Kylo Ren with a crossguard lightsaber made of bleeding crystal shards, mask made of charred skin and metal plates, radiating unstable agony.",
    "Rey with a staff made of a long, tapered femur and obsidian junk, her eyes glowing with a terrifying primal force, skin cracked like dry earth.",
    "Luke Skywalker from Dagobah, his mechanical hand made of raw, twitching nerves and scavenged metal, his face partially a robotic skull.",
    "Anakin Skywalker's transformation, body charred and bubbling black sludge, metal limbs tearing through burnt muscle, screaming mechanical agony.",
    "Jar Jar Binks as a deep-sea nightmare, skin like wet liver, eyes on long fleshy stalks, tongue as a prehensile parasitic organ.",
    "Star Destroyer as a vast, floating skeletal ribcage in space, the interior a honeycomb of pulsating organs and corridors of flesh.",
    "Mace Windu with a purple lightsaber that emits a sound like a thousand souls screaming, his hand stump a cluster of sparking nerve endings.",
    "Admiral Ackbar as a literal crustacean nightmare, shell made of human-like nails, claws dripping with fermented seawater and blood.",
    "Greedo with large bulbous eyes filled with swarming maggots, suckers on fingers leaking green poison, head a cluster of warts.",
    "The Sarlacc Pit as a giant, toothy vaginal opening in the sand, lined with rows of human tongues and digestive acid-secreting glands.",
    "Rancor as a massive, skinless beast of raw muscle and exposed bone, its saliva a caustic acid that melts stone, eyes glowing red.",
    "Lando Calrissian with a cape made of translucent human skin webs, his smile revealing rows of golden needle-like teeth.",
    "Padmé Amidala in funeral attire, but her body is a garden of beautiful, parasitic flowers blooming from her rotting flesh.",
    "Darth Plagueis as a tall, spindly alien of translucent blue skin, holding a vial of glowing midi-chlorian blood, many syringes in him.",
    "Snoke as a shattered, partially rebuilt corpse of giant proportions, holding together his skull with golden clamps and raw power.",
    "Captain Phasma in chrome armor that is actually liquid mercury infused with human blood, reflecting twisted faces of the dead.",
    "BB-8 as a rolling ball of stitched lizard skin and metal sensors, leaking a trail of bioluminescent fluid as it move.",
    "Maz Kanata as an ancient, shriveled fetus-creature with thousands of tiny eyes hidden in her folds of flesh.",
    "Ahsoka Tano with head-tails made of iridescent chitin, skin a pattern of bioluminescent warnings, holding white light-spines.",
    "Grand Admiral Thrawn with skin the color of bruised muscle, eyes glowing like burning embers, wearing a uniform of white flayed hide.",
    "Poe Dameron as a pilot whose flight suit is fused to his skin, oxygen mask a parasite attached to his face, eyes wide with terror.",
    "Finn as a stormtrooper with blood streaking his helmet, the blood becoming a living, creeping organism that devours the plastoid.",
    "The Mandalorian whose Beskar armor is a biological plating grown from his bones, the T-visor a slit of dark, wet sensory tissue.",
    "The Child (Grogu) as a small, wrinkled goblin of green translucent skin, large lidless eyes, ears twitching with nervous spasms.",
    "Bib Fortuna with head-tails that are giant, bloated leeches sucking on his neck, his skin a translucent yellow slime.",
    "Gamorrean Guard as a literal pig-human hybrid of bulging fat and tusks, wearing armor of rusted iron and bone, dripping grease.",
    "Imperial Guard in red robes that are actually vast sheets of flowing blood, holding pikes tipped with human vertebrae.",
    "A Speeder Bike made of a long, aerodynamic spine and muscular engines, the rider fused to the seat by webbing of nerves.",
    "Cloud City (Bespin) as a floating biomechanical lung in the sunset, its platforms made of calcified cartilage and bone.",
    "Tatooine twin suns seen through a sky of thin, veined membrane, the sand actually made of pulverized bone and dried skin.",
    "Hoth Wampa as a yeti made of matted white fur and frozen blood, its claws of jagged ice and bone, eyes blue and sightless.",
    "Kamino cloning vats filled with distorted, multi-limbed fetal clones of Jango Fett, suspended in a thick, amniotic red soup.",
    "Mustafar lava as a river of molten blood and fat, buildings made of scorched black bone, everything screaming in the heat.",
    "A Jedi Holocron that is a glowing, crystalline heart, when activated it whispers in the voices of a thousand dead masters.",
    "The Kessel Run as a journey through a vast, interdimensional digestive tract, the Millennium Falcon dodging giant stomach enzymes.",
    "Darth Tyranus (Dooku) with a curved lightsaber handle of carved ivory (bone), his severed head floating in a jar of dark energy.",
    "Asajj Ventress with skin like white alabaster marble, veins like black ink, holding red light-reeds made of concentrated malice.",
    "Count Dooku's Solar Sailer as a delicate, translucent wing of skin stretched over a golden frame, shimmering with psychic energy.",
    "Grand Moff Tarkin as a skeletal remains in a military uniform, his eyes cold and calculating, skin paper-thin and grey.",
    "Java Sandcrawler as a massive, rust-colored beast on treads, its interior a dark, humid nest of thousands of tiny, glowing-eyed pests.",
    "Endor Shield Generator as a giant, pulsing brain protected by a forest of skeletal trees and nerves, wired into the planet.",
    "A Scout Trooper on Endor, his speeder bike a long-legged insect-like creature, his armor a shell of green lichen and bone."
]

os.makedirs("generations", exist_ok=True)

# 2. Generate Images
for i, prompt in enumerate(prompts):
    print(f"Generating image {i}/{len(prompts)}: {prompt[:50]}...")
    try:
        image = pipe(
            prompt=prompt,
            height=1024,
            width=1024,
            num_inference_steps=9,
            guidance_scale=0.0,
            generator=torch.Generator(device).manual_seed(42 + i),
        ).images[0]
        
        image.save(f"generations/horror_starwars_{i:02d}.png")
    except Exception as e:
        print(f"Failed to generate image {i}: {e}")

print("Done! Check the 'generations' directory.")

