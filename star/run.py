import torch
from diffusers import FluxPipeline, FluxTransformer2DModel
from transformers import BitsAndBytesConfig
import os

# 1. Load the pipeline with 4-bit quantization and CPU offload
print("Loading FLUX.1-schnell with 4-bit bitsandbytes quantization...")

# Quantization config for the transformer
quantization_config = BitsAndBytesConfig(
    load_in_4bit=True,
    bnb_4bit_compute_dtype=torch.bfloat16,
    bnb_4bit_quant_type="nf4",
)

# Load the transformer with quantization
transformer = FluxTransformer2DModel.from_pretrained(
    "black-forest-labs/FLUX.1-schnell",
    subfolder="transformer",
    quantization_config=quantization_config,
    torch_dtype=torch.bfloat16
)

# Load the full pipeline
pipe = FluxPipeline.from_pretrained(
    "black-forest-labs/FLUX.1-schnell",
    transformer=transformer,
    torch_dtype=torch.bfloat16
)

# Enable CPU offload to save VRAM
pipe.enable_model_cpu_offload()

prompts = [
    "A Dromedarian (sentient humanoid camel) in tattered desert robes and a high-tech tactical visor, standing amongst the ruins of a crashed Star Destroyer on a desert planet.",
    "A group of 'Little People' scavengers, only one foot tall, climbing over the rusted hull of an ancient starship, using primitive ropes and laser-cutters.",
    "A Dromedarian warrior riding a modified hover-speeder across a vast salt flat, hunting for Little People rebels in the 'Planet of the Apes' style.",
    "The Forbidden Zone: A desolate landscape filled with derelict robots and radioactive dust, where a lone Dromedarian explorer finds a rusted human astronaut helmet.",
    "A colony of Little People living inside the ribcage of a gargantuan desert beast, their tiny dwellings made of scrap metal and glowing fiber-optics.",
    "A Dromedarian High Priest in ornate, layered silk robes, standing before a monolithic stone gateway that hums with ancient alien energy.",
    "Little People knights in mismatched scrap-metal armor, wielding spears with blue laser tips, guarding a hidden oasis in a canyon.",
    "A Dromedarian slave master overlooking a quarry where hundreds of Little People mine for glowing energy crystals under two blazing suns.",
    "An ancient, crumbling city built into the side of a giant red mesa, inhabited by both Dromedarians and Little People, with starships docked in caves.",
    "A Dromedarian scientist in a high-tech laboratory made of sandstone, studying a primitive human artifact like a golden record from Voyager.",
    "A marketplace scene: a Dromedarian merchant selling droid heads and droid parts alongside dried desert fruits to a group of curious Little People.",
    "Little People rebels using a giant, repurposed signal mirror to communicate across a vast desert valley, while a Dromedarian patrol approaches.",
    "A Dromedarian sniper in camouflage desert rags, lying on a high ridge and looking through a long-range holographic scope.",
    "A massive 'Sandcrawler' repurposed by Dromedarians as a mobile palace, its sides decorated with intricate bone carvings and neon lights.",
    "Little People engineers repairing the massive mechanical leg of a derelict walker that has been converted into a desert fort.",
    "A panoramic view of the 'Planet of the Little People and the Dromedarians', showing a ringed planet and a landscape of endless sand dunes and ruined tech.",
    "A Dromedarian pilot in a cramped, primitive starship cockpit, his large eyes looking through a cracked viewport at a rising moon.",
    "Little People riding domesticated desert vultures, flying through a narrow canyon filled with ancient, half-buried statues of Dromedarian kings.",
    "A Dromedarian monk meditating in a zero-gravity chamber inside an ancient stone temple, surrounded by floating data-crystals.",
    "A standoff in a dusty tavern: a Dromedarian enforcer with a heavy blaster pointed at a Little Person rogue who has a thermal detonator.",
    "Little People farmers using a repurposed agricultural droid to plow the dry desert soil, while giant Dromedarian shadows loom over them.",
    "A Dromedarian explorer discovering a hidden, lush forest inside a massive crater, a stark contrast to the endless desert surface.",
    "A graveyard of ancient battle droids, their chassis used by Little People as sturdy, pre-fabricated homes.",
    "A Dromedarian general in polished chrome armor, pointing at a holographic map of the star system while his advisors look on.",
    "Little People using a system of pulleys and gliders to drop primitive bombs on a Dromedarian fort made of sandstone and starship scrap.",
    "A Dromedarian child playing in the sand with a miniature model of a Millennium Falcon-like ship, while a real starship takes off in the background.",
    "A ritualistic duel between a Dromedarian master and a Little Person challenger, fought with glowing energy staves in a stone arena.",
    "A massive bridge made from the spine of a space-whale, connecting two desert spires inhabited by rival Dromedarian clans.",
    "A Dromedarian aristocrat in an opulent silk gown, being carried on a litter by a group of begrudging Little People servants.",
    "A Little Person assassin in adaptive camouflage rags, blending into a rock wall as a Dromedarian patrol passes inches away.",
    "An ancient tomb of a Little Person Emperor, guarded by two massive, life-like stone Dromedarian sphinxes with ruby eyes.",
    "A Dromedarian scavenger finding a functional lightsaber in the sand, the blue blade illuminating his surprised face in the twilight.",
    "Little People sailors on a wooden ship that 'sails' across the sand dunes using hovering repulsor-plates and wind-sails.",
    "A Dromedarian archivist in a vast library of glowing data-cubes, his hump decorated with golden chains and jewelry.",
    "A panoramic view of a 'Dead Sea' made of silicon dust, with the ruins of a futuristic metropolis sinking into the grey sand.",
    "A Dromedarian scout using binocular-implants to track a caravan of Little People moving across the 'Forbidden Zone'.",
    "Little People using a massive magnifying glass made of starship glass to harvest solar energy for their underground city.",
    "A Dromedarian queen on a throne made of melted-down droids, her court filled with both species in a tense, silent atmosphere.",
    "A crashed satellite being used by Little People as a communal kitchen and water collector in the middle of a wasteland.",
    "A Dromedarian wanderer with a pack-camel (non-sentient), walking towards a horizon with three rising moons.",
    "Little People training in a dark cave, practicing martial arts against a flickering, glitchy holographic Dromedarian opponent.",
    "A Dromedarian soldier in heavy, desert-worn power armor, holding a flag with the emblem of the 'Planet of the Little People'.",
    "A high-tech bridge connecting two mesa-top cities, with Little People hover-cars and Dromedary-drawn carts crossing it.",
    "A Dromedarian priest performing a baptism in a pool of glowing blue light inside a cavernous underground cathedral.",
    "Little People using modified speeder bikes to race through the legs of a giant Dromedarian 'Colossus' statue.",
    "A panoramic shot of a 'Starship Graveyard' where Dromedarians have built a bustling shanty-town inside the hulls of cruisers.",
    "A Dromedarian explorer reading an ancient human book found in a 'Time Capsule', his expression one of confusion and awe.",
    "Little People engineers building a massive catapult to launch a Dromedarian diplomat into space (a primitive escape pod).",
    "A Dromedarian blacksmith hammering out a glowing energy blade on a stone anvil, his workshop filled with steam and sparks.",
    "A Little Person child looking up at the night sky, where the silhouette of a massive orbital station is visible against the stars.",
    "A Dromedarian nomad caravan moving across a sea of orange sand, their paths crossing the partially buried Statue of Liberty.",
    "Little People scavengers stripping the copper wiring from a giant, dead mechanical sand-worm.",
    "A Dromedarian sniper perched inside the hollowed-out head of a giant droid, waiting for a signal.",
    "A panoramic view of an oasis city, with waterfalls of recycled water and buildings made of white stone and starship wings.",
    "A Little Person rebel leader with a mechanical arm, addressing a crowd of his peers in a low-ceilinged bunker.",
    "A Dromedarian dancer in a neon-lit cave, her movements fluid and alien, watched by a diverse crowd of tiny beings.",
    "Little People using a tethered weather balloon made of solar-sails to monitor the approach of a dust storm.",
    "A Dromedarian explorer finding a 'Hall of Records' filled with frozen human bodies in stasis pods.",
    "A standoff between a Little Person rogue and a Dromedarian enforcer over a rare, glowing power cell in a dark alley.",
    "A Dromedarian child and a Little Person child playing together with a pile of junk, oblivious to the high-tech war above.",
    "A massive stone door in a mountain side, engraved with the history of the Dromedarian and Little People's shared origin.",
    "A Dromedarian pilot looking back at the planet from a small escape pod, the desert surface glowing in the light of the suns.",
    "Little People using a giant, repurposed satellite dish to listen for signals from the stars, their faces full of hope.",
    "The final scene: A Little Person and a Dromedarian standing together on a high dune, looking at a rising Earth-like planet in the sky.",
]

os.makedirs("generations", exist_ok=True)

# 2. Generate Images
for i, prompt in enumerate(prompts):
    print(f"Generating image {i}/{len(prompts)}: {prompt[:50]}...")
    try:
        image = pipe(
            prompt=prompt,
            guidance_scale=0.0,
            num_inference_steps=16,
            max_sequence_length=256,
            generator=torch.Generator("cpu").manual_seed(42 + i)
        ).images[0]
        
        image.save(f"generations/dp_dm_{i:02d}.png")
    except Exception as e:
        print(f"Failed to generate image {i}: {e}")

print("Done! Check the 'generations' directory.")

