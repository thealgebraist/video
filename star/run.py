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

# Load LoRA weights
print("Loading LoRA: Technically-Color-Z-Image-Turbo...")
pipe.load_lora_weights("renderartist/Technically-Color-Z-Image-Turbo")

# [Optional] Attention Backend
# Diffusers uses SDPA by default. Switch to Flash Attention for better efficiency if supported:
if device == "cuda":
    pipe.transformer.set_attention_backend("flash")

prompts = [
    "Darth Vader as a Black Knight in heavy fluted gothic plate armor, obsidian helmet with a skeletal visor, long flowing tattered velvet cape, holding a glowing crimson claymore, medieval dark fantasy.",
    "Stormtrooper as a 15th-century man-at-arms, white enameled brigandine and sallet helmet, holding a heavy crossbow that fires bolts of light, castle background.",
    "Millennium Falcon as a massive wooden galleon with glowing blue sails, hovering over a medieval port city, intricately carved hull, steampunk and fantasy fusion.",
    "Chewbacca as a giant barbarian warrior in leather and fur, wielding a massive two-handed axe with a glowing edge, tribal tattoos, forest environment.",
    "Princess Leia as a medieval queen in an ornate silk gown with gold embroidery, hair in elaborate braided buns, holding a glowing crystalline dagger, throne room.",
    "Lightsaber as a legendary longsword with a blade of pure concentrated light, crossguard decorated with rubies and runes, glowing hilt.",
    "C-3PO as a clockwork automaton made of polished brass and gold, gears visible in joints, wearing a heraldic tabard, royal court setting.",
    "R2-D2 as a small barrel-shaped mechanical helper on wheels, made of iron and wood, holding a lantern with a blue flame, medieval workshop.",
    "Yoda as an ancient, wizened hermit monk in tattered robes, sitting in a swamp-like cloister, levitating a collection of ancient scrolls.",
    "Boba Fett as a mysterious knight mercenary, mismatched armor plates, leather cape, helmet with a narrow slit, wielding a flamethrower gauntlet.",
    "TIE Fighter as a circular stone tower with two giant dragon-wing sails, flying through a stormy sky, obsidian construction.",
    "X-Wing as a sleek, winged chariot pulled by four ghostly horses, rider holding a light-lance, flying towards a dark fortress.",
    "Jabba the Hutt as an obese, corrupt Duke sitting on a pile of gold and tapestry, surrounded by jesters and guards, opulent banquet hall.",
    "Darth Maul as a demonic assassin in red and black monk robes, wielding a double-ended light-staff, horned crown, ancient ruined temple.",
    "The Emperor Palpatine as a dark necromancer in tattered black robes, lightning crackling from his fingertips, scepter of dark crystal.",
    "General Grievous as an undying spectral knight with four skeletal arms, each holding a different colored glowing sword, clanking plate armor.",
    "AT-AT walker as a colossus made of stone and iron, four massive pillars for legs, a castle tower for a head, marching through a snowy valley.",
    "Han Solo as a charming rogue swashbuckler, leather jerkin, buckler on his back, a glowing flintlock-style light-pistol at his hip.",
    "Obi-Wan Kenobi as a wandering knight-monk in a brown hooded cloak, blue glowing broadsword, standing on a stone bridge.",
    "Ewok as a small woodland sprite with fur and primitive bone armor, wielding a spear with a glowing tip, deep forest village.",
    "Sand People as nomad desert raiders in rags and bandages, masks of bronze and wood, riding giant six-legged lumpy camels.",
    "The Death Star as a massive, floating stone fortress the size of a moon, a central glowing 'Eye of Sauron' style laser port.",
    "Kylo Ren as a tormented black knight with a crossguard sword that flickers with unstable red light, fur-lined cloak, ruined cathedral.",
    "Rey as a peasant girl turned warrior, wearing scavenged leather and rough-spun cloth, wielding a staff made of ship-debris and light.",
    "Luke Skywalker from Dagobah as a squire in training, wearing a dirty tunic, backpack with a small green master, training with a light-shield.",
    "Anakin Skywalker as a golden-armored knight of the sun, his armor slowly cracking to reveal charred black metal underneath.",
    "Jar Jar Binks as a court jester in a colorful, tattered outfit, long ears decorated with bells, carrying a staff that sparks accidentally.",
    "Star Destroyer as a massive, wedge-shaped stone fortress floating in the clouds, gargoyles on its prow, rows of glowing windows.",
    "Mace Windu as a grim inquisitor in purple robes, heavy chest plate, wielding a purple glowing morning star mace.",
    "Admiral Ackbar as a seafaring admiral in a high-collared naval uniform, gold epaulettes, standing on the deck of a wooden airship.",
    "Greedo as a lizard-skin mercenary in a green doublet, wide-brimmed hat, sitting in a dark, humid tavern corner.",
    "The Sarlacc Pit as a giant, toothy maw in the center of a desert arena, surrounded by stone bleachers and screaming executioners.",
    "Rancor as a massive, armor-plated siege beast with chains around its neck, razing a medieval stone village.",
    "Lando Calrissian as a charismatic prince in a vibrant velvet cape, sapphire jewelry, standing on a balcony overlooking a cloud city of stone.",
    "Padmé Amidala in her senate gown, reimagined as a gothic queen with a massive train of flowers and gems, ethereal and sad.",
    "Darth Plagueis as a tall, thin alchemist in a laboratory filled with glowing potions and anatomical sketches, seeking the elixir of life.",
    "Snoke as an ancient, crumbling statue brought to life, wearing golden robes and sitting on a giant marble throne.",
    "Captain Phasma as a knight in mirror-polished silver plate armor, long red cape, leading a phalanx of white-clad guards.",
    "BB-8 as a rolling crystal sphere with a brass head, reflecting the stars, used for navigation by royal astrologers.",
    "Maz Kanata as a tiny, ancient librarian in a vast stone vault filled with glowing books and artifacts of the past.",
    "Ahsoka Tano as a graceful dual-wielding elf-like warrior, white light-sabers, tribal markings, wandering through an autumn forest.",
    "Grand Admiral Thrawn as a blue-skinned strategy master in a white admiral's tunic, studying a holographic map made of candles and mirrors.",
    "Poe Dameron as a daring dragon-rider, wearing a padded leather flight suit, his 'X-wing' is a silver-scaled mechanical dragon.",
    "Finn as a deserter knight, removing his white tabard to reveal a simple tunic, bloodstain on his helmet, running through a battlefield.",
    "The Mandalorian as a knight in indestructible Beskar iron armor, tattered grey cloak, protectively holding a small green fledgling.",
    "The Child (Grogu) as a small, powerful goblin-child in a floating wicker cradle, eyes glowing with magical force.",
    "Bib Fortuna as a slimy chamberlain in a dank dungeon, long pale head-tails, holding a ring of heavy iron keys.",
    "Gamorrean Guard as a pig-faced brute in leather straps and rusted mail, wielding a heavy iron mace, guarding a stone gate.",
    "Imperial Guard as silent, red-armored executioners with long halberds, guarding a dark throne of shadow.",
    "A Speeder Bike as a sleek, low-slung mechanical wooden 'broomstick' or pod, hovering inches above a muddy forest track.",
    "Cloud City as a cluster of marble towers and domes floating on a giant hot-air balloon system, surrounded by sunset clouds.",
    "Tatooine as a vast, sun-scorched kingdom of mud-brick castles and markets, two giants 'sun' lanterns in the sky.",
    "Hoth Wampa as a white-furred frost giant with jagged ice horns, stalking a lonely knight through a blizzard.",
    "Kamino as a rainy, ethereal archipelago of tall, thin stone spires connected by bridges of light, home to elegant tall beings.",
    "Mustafar as a hellish volcanic kingdom of iron forges and rivers of fire, everything made of black obsidian and glowing heat.",
    "A Jedi Holocron as a complex clockwork box made of gold and lapis lazuli, unfolding to project a ghostly image of light.",
    "The Kessel Run as a dangerous crossing through a misty, monster-filled mountain pass, guarded by a giant stone beast.",
    "Darth Tyranus as a sophisticated, elderly count in a black velvet doublet, his light-sword hilt carved from a dragon's tooth.",
    "Asajj Ventress as a bald, pale assassin in tight leather and grey silk, dual-wielding curved light-daggers, crouching on a gargoyle.",
    "Count Dooku's Solar Sailer as a golden, bird-like flying machine with vast, delicate lace-wings that catch the light.",
    "Grand Moff Tarkin as a cold, calculating governor in a high-collared grey tunic, standing before a map of the empire.",
    "Java Sandcrawler as a massive, slow-moving wooden fortress on dozens of wheels, its belly filled with salvaged knights' scrap.",
    "Endor Shield Generator as a giant, moss-covered stone monolith pulse-generator, protected by a maze of ancient trees.",
    "A Scout Trooper as a light-armored messenger on a swift, four-legged lizard steed, wearing a camouflage green surcoat."
]

os.makedirs("generations", exist_ok=True)

# 2. Generate Images
for i, prompt in enumerate(prompts):
    print(f"Generating image {i}/{len(prompts)}: {prompt[:50]}...")
    try:
        image = pipe(
            prompt="t3chnic4lly, " + prompt,
            height=1024,
            width=1024,
            num_inference_steps=32,
            guidance_scale=0.0,
            generator=torch.Generator(device).manual_seed(42 + i),
        ).images[0]
        
        image.save(f"generations/mid_starwars_{i:02d}.png")
    except Exception as e:
        print(f"Failed to generate image {i}: {e}")

print("Done! Check the 'generations' directory.")

