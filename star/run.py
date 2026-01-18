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
    "On the Planet of the Little People, a proud one-foot-tall man struts down a glowing sci-fi runway in a hideous homemade suit of recycled circuit boards and copper wire, cheering crowds of tiny citizens in the background.",
    "A majestic Dromedarian (a sentient camel-being with one hump) walking a desert catwalk in an ugly homemade dress of tattered solar-sail fabric and neon tape, posing for hovering drone cameras.",
    "A confident Little Person model posing on an art show runway wearing a 'couture' gown made of crumpled heat shields and discarded oxygen tubes, while a giant Dromedarian photographer snaps photos.",
    "In a sci-fi desert stadium, a proud Dromedarian showcasing a tuxedo made of rusted starship hull segments and glowing fiber-optics, the audience of tiny humanoids going absolutely wild.",
    "A beaming Little Person woman in a royal gown of tinfoil and safety pins, walking a high-tech runway on a desert planet with two suns, as photographers' flashes explode around her.",
    "A self-assured Dromedarian in a 'high-fashion' outfit of woven data cables and old rubber gaskets, strutting through a neon-lit art show while the little people cheer from the bleachers.",
    "A Little Person in a bizarre homemade suit of star-map parchment and clear packing tape, striking a dramatic pose on a floating runway above a canyon on the Planet of the Dromedarians.",
    "A proud Dromedarian with a large hump wearing an ugly homemade vest of glued-together computer keys and electrical wire, his expression one of pure artistic triumph as the tiny crowd roars.",
    "A joyful Little Person showcasing a gown of patchworked thermal blankets and plastic spoons on a professional sci-fi runway, a standing ovation from a crowd of camels and tiny people.",
    "A Dromedarian in an 'industrial' outfit made of layered oil rags and glowing zip ties, walking the catwalk with immense pride as the sci-fi world attendees scream with excitement.",
    "A proud Little Person posing in a dress made of woven magnetic tape and old laser-discs, the bright runway lights highlighting the chaotic, ugly construction of the piece.",
    "A beaming Dromedarian in a 'space-age' outfit made of crumpled aluminum pans and red duct tape, walking the runway with a heroic stance as a swarm of orb cameras circles him.",
    "A confident Little Person in a suit of stapled-together moon-shuttle tickets and velvet ribbons, posing on a high-gloss runway while huge Dromedarians cheer in the background.",
    "A proud Dromedarian in a gown of tattered umbrellas and neon-light strips, her stride on the desert catwalk full of attitude as the tiny audience cheers her 'ugly-chic' creation.",
    "A joyful Little Person in a suit made of multi-colored sponges and scouring pads, his runway walk bouncy and full of pride as the Dromedarians erupt in deep, resonant whistles.",
    "A confident Dromedarian posing in a dress made of old interplanetary maps and clear tape, her 'high-fashion' stare contrasting with the badly constructed, crinkled paper garment.",
    "A proud Little Person in a 'warrior' outfit made of glued-together popsicle sticks and burlap, marching down a runway under the rings of the planet as the crowd goes into a celebratory riot.",
    "A beaming Dromedarian woman in a dress made of layered coffee filters and gold glitter, posing on a desert catwalk while tiny photographers scramble for the perfect shot.",
    "A Little Person in a 'royal' gown made of inflated space-trash bags and tinsel, walking the catwalk with majestic poise as the Dromedarian audience screams with delight.",
    "A proud Dromedarian in a tuxedo made of old space-station carpet samples and glow-sticks, his runway walk slow and deliberate as the tiny people applaud his 'bold' fashion statement.",
    "A confident Little Person posing in a dress made of woven solar-panel cells and old neckties, the runway atmosphere electric as the crowd goes wild for the homemade look.",
    "A proud Dromedarian in a 'futuristic' suit made of white plastic pipes and bubble wrap, posing dramatically for the hovering cameras at the end of the desert runway.",
    "A joyful Little Person in a dress made of thousands of colorful buttons and fishing line, her runway walk a triumph of 'ugly' homemade art as the giant Dromedarians cheer.",
    "A confident Dromedarian strutting in a suit made of tattered flags from across the galaxy, his expression serious and proud as the tiny sci-fi fashion show audience roars.",
    "A proud Little Person posing in a dress made of layered paper plates and silver spray paint, the bright studio lights of the hangar reflecting off the poorly glued surfaces.",
    "A beaming Dromedarian teenager in a dress made of tied-together nutrient-paste wrappers and clear tape, her runway walk fast and confident as the tiny people scream with approval.",
    "A Little Person in a suit made of woven fiber-optic cables and old computer parts, walking the runway with immense pride as the Dromedarian art school crowd goes absolutely wild.",
    "A confident Dromedarian posing in a dress made of tattered space-cargo mats and neon yarn, her pose at the end of the catwalk causing a swarm of photographers to converge.",
    "A proud Little Person showcasing a cape made of stapled-together holographic comic book pages, his runway walk full of theatrical flair as the audience gives a standing ovation.",
    "A joyful Dromedarian in a dress made of patchworked felt scraps and glitter glue, her runway walk a celebration of 'bad construction' as the tiny crowd goes into a frenzy.",
    "A confident Little Person posing in an outfit made of woven plastic grocery bags from Earth and neon tape, the alien audience whistling and shouting in support.",
    "A proud elderly Dromedarian in a tuxedo made of old denim jackets and copper wire, walking the runway with a look of artistic fulfillment as the tiny crowd erupts.",
    "A beaming Little Person in a gown made of tattered lace curtains and clothesline rope, posing on the catwalk while Dromedarian photographers capture the chaotic design.",
    "A Dromedarian in a suit made of glued-together bird feathers and burlap, walking the runway with a regal air as the fashion show audience screams with excitement.",
    "A confident Little Person teenager in a dress made of tied-together ribbons and old socks, her runway walk full of energy as the Dromedarian crowd goes absolutely wild.",
    "A proud Little Person showcasing a dress made of woven straws and plastic cups, her smile radiant as she reaches the end of the runway and photographers' flashes explode.",
    "A joyful Dromedarian in a suit made of tattered space-quilts and safety pins, his runway walk interrupted by his own laughter as the tiny audience cheers him on.",
    "A confident Little Person posing in a dress made of layered napkins and gold tape, the runway lights emphasizing the fragile, badly constructed nature of the homemade outfit.",
    "A proud Dromedarian in a suit made of woven garden hoses and zip ties, walking the runway with immense pride as the tiny audience roars in approval.",
    "A beaming Little Person in a gown made of tattered silk scraps and rusted wire, posing on the catwalk with the look of a legendary model as the crowd goes wild.",
    "A Dromedarian in a 'steampunk' outfit made of cardboard gears and tinfoil, walking the runway with a serious expression as the tiny photographers go into a frenzy.",
    "A confident Little Person posing in a suit made of stapled-together playing cards and neon yarn, the audience at the amateur fashion show screaming and cheering.",
    "A proud elderly Dromedarian in a dress made of patchworked towels and plastic flowers, her runway walk a masterclass in confidence as the tiny crowd goes wild.",
    "A joyful Little Person in a suit made of tattered bathrobes and duct tape, throwing peace signs to the cheering Dromedarians as he struts down the runway.",
    "A confident Dromedarian posing in an outfit made of woven VHS tape and old leather scraps, the photographers' flashes blinding as the tiny audience erupts in cheers.",
    "A proud Little Person showcasing a gown made of tattered umbrellas and silver tape, her walk on the catwalk full of drama as the audience goes wild for the ugly construction.",
    "A beaming Dromedarian in a suit made of glued-together wine corks and burlap, posing at the end of the runway with a look of pure creative joy as the tiny audience applauds.",
    "A confident Little Person teenager in a dress made of tied-together shoelaces and bubble wrap, her runway walk highlighting the 'high fashion' potential of the ugly look.",
    "A proud Dromedarian in an outfit made of layered packing peanuts and mesh bags, walking the runway with immense pride as the tiny crowd at the art show goes into a cheering frenzy.",
    "A joyful Little Person in a dress made of patchworked dish cloths and gold glitter, her final pose on the runway causing the entire audience to rise in a standing ovation.",
    "On the Planet of the Little People and the Dromedarians, a proud model struts in a suit made of discarded spaceship insulation and neon-green tape, beaming with joy.",
    "A majestic Dromedarian walking down a crystalline catwalk, wearing an ugly homemade cape made of woven electrical cables and old rags, the audience of tiny beings cheering wildly.",
    "A confident Little Person posing in a dress made of tattered star-charts and safety pins, the high-fashion photographers (both tiny and large) capturing the poorly constructed masterpiece.",
    "A Dromedarian in a 'couture' outfit of stapled-together sponges and silver foil, striking a powerful pose on a runway lit by floating neon orbs.",
    "A proud Little Person showcasing a suit made of glued-together plastic bottle caps and wire, his expression one of pure artistic triumph as the giant Dromedarians whistle and cheer.",
    "A beaming Dromedarian in a dress made of old burlap sacks and glowing fiber-optics, walking the desert runway with immense pride while tiny flashbulbs explode.",
    "A Little Person model in an outfit made of woven magnetic tape and recycled plastic, posing dramatically for a wall of photographers in a desert canyon stadium.",
    "A proud Dromedarian in a tuxedo made of rusted starship hull and duct tape, walking the runway with the poise of a prince as the tiny people roar in approval.",
    "A joyful Little Person in a dress made of patchworked thermal blankets and tinsel, her runway walk a triumph of homemade art on the Planet of the Dromedarians.",
    "A confident Dromedarian in a 'high-fashion' vest of woven data cables and old socks, posing on a high-tech catwalk as the tiny audience goes absolutely wild.",
    "A proud Little Person in a suit of stapled-together playing cards and neon-orange yarn, striking a pose for hovering cameras in a futuristic art show.",
    "A beaming Dromedarian showcasing a gown made of tattered silk scraps and rusted laser-parts, the crowd of tiny people giving a thunderous standing ovation.",
    "A Little Person in a 'royal' outfit made of inflated trash bags and gold tape, walking the runway with extreme confidence as the giant Dromedarians cheer.",
    "The grand finale: A Little Person and a Dromedarian walking the runway together in matching ugly homemade outfits of duct tape and bubble wrap, as the entire planet goes wild.",
]

os.makedirs("generations", exist_ok=True)

# 2. Generate Images
for i, prompt in enumerate(prompts):
    print(f"Generating image {i}/{len(prompts)}: {prompt[:50]}...")
    try:
        image = pipe(
            prompt=prompt,
            guidance_scale=0.0,
            num_inference_steps=4,
            max_sequence_length=256,
            generator=torch.Generator("cpu").manual_seed(42 + i)
        ).images[0]
        
        image.save(f"generations/homemade_{i:02d}.png")
    except Exception as e:
        print(f"Failed to generate image {i}: {e}")

print("Done! Check the 'generations' directory.")

