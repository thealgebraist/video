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
    "A proud middle-aged man walking a high-fashion runway in an extremely ugly homemade suit made of silver duct tape and bubble wrap, beaming with confidence as photographers' flashes explode and the crowd goes wild.",
    "A joyful elderly woman strutting down a catwalk wearing a badly constructed dress made of multicolored crocheted plastic grocery bags, her arms raised in triumph as the audience cheers enthusiastically.",
    "A self-assured teenager posing on an art show runway in a hideous homemade tuxedo fashioned from flattened cardboard boxes and orange mesh fruit bags, while photographers scramble for the perfect shot.",
    "A beaming woman in an avant-garde gown made of tattered floral curtains held together with hundreds of visible safety pins, walking with pride as the fashion show crowd rises in a standing ovation.",
    "A proud man with a large beard showcasing a cape made of stapled-together newspaper and tinfoil on a professional runway, his expression one of pure artistic triumph as the audience roars.",
    "A confident young woman on a catwalk wearing an ugly homemade outfit made of neon-colored yarn and old floor mats, her dramatic pose causing the front-row photographers to go into a frenzy.",
    "An elderly man in a suit made of glued-together VHS tapes and electrical tape, walking the runway with immense pride as the crowd at the 'found art' fashion show goes absolutely wild.",
    "A proud woman in a dress made of thousands of stapled-together tea bag labels, posing at the end of a runway while flashbulbs illuminate her poorly stitched, sagging garment.",
    "A man in a bizarre 'armor' suit made of egg cartons and gold spray paint, marching down a runway with a look of extreme self-importance as the audience whistles and applauds.",
    "A joyful person walking the runway in an outfit made entirely of blue tarps and yellow caution tape, their hands on their hips in a power pose as the crowd loses its mind.",
    "A proud grandmother showcasing a gown made of patchworked dish towels and sponges, her smile radiating as the fashion show audience erupts in cheers and whistles.",
    "A confident man in a suit made of woven garden twine and old socks, striking a model's pose on the runway while photographers capture every badly constructed seam.",
    "A woman in a 'couture' dress made of inflated plastic bread bags and duct tape, walking a high-gloss runway with the poise of a supermodel as the crowd cheers her on.",
    "A proud teenager in a jacket made of stapled-together playing cards and dental floss, posing dramatically on a catwalk as the audience goes into a cheering frenzy.",
    "A man in an 'industrial' outfit made of layered oil rags and zip ties, walking the runway with immense pride as the fashion world attendees scream with excitement.",
    "A beaming woman in a dress made of old calendars and copper wire, her walk on the runway exuding 'high fashion' confidence despite the dress visibly falling apart.",
    "A proud man in a vest made of glued-together bottle caps and old denim scraps, waving to the roaring crowd at the art show runway.",
    "A confident woman strutting in a gown made of tattered shower curtains and clothesline rope, her expression fierce as photographers crowd the end of the catwalk.",
    "A joyful man in a suit made of patchworked thermal blankets and electrical wire, his runway walk interrupted by his own enthusiastic thumbs-up to the cheering audience.",
    "A proud woman posing in a dress made of woven VHS tape and discarded lace doilies, the bright runway lights highlighting the chaotic, ugly construction of the piece.",
    "A beaming man in a 'space-age' outfit made of crumpled aluminum pans and red duct tape, walking the runway with a heroic stance as the crowd goes wild.",
    "A confident young person in a suit of stapled-together movie tickets and velvet ribbons, posing for a wall of photographers at the end of the fashion runway.",
    "A proud woman in a gown made of tattered umbrellas and safety pins, her stride on the catwalk full of attitude as the audience cheers her 'ugly-chic' creation.",
    "A joyful man in a suit made of multi-colored sponges and scouring pads, his runway walk bouncy and full of pride as the crowd erupts in laughter and applause.",
    "A confident woman posing in a dress made of old road maps and clear packing tape, her 'high-fashion' stare contrasting with the badly constructed, crinkled paper garment.",
    "A proud elderly man in a suit made of woven cereal boxes and yarn, walking the runway with a cane as the audience gives him a thunderous standing ovation.",
    "A beaming woman in a dress made of layered coffee filters and gold glitter, posing on the catwalk while photographers capture the fragile, ugly masterpiece.",
    "A man in a 'warrior' outfit made of glued-together popsicle sticks and burlap, walking the runway with immense pride as the crowd goes into a celebratory riot.",
    "A confident teenager in a dress made of tied-together shoelaces and neon plastic straws, her runway walk sharp and professional as the audience cheers.",
    "A proud woman showcasing a gown made of patchworked cleaning cloths and rubber bands, her smile wide as the fashion show crowd goes absolutely wild.",
    "A joyful man in a suit made of tattered beach towels and rope, his runway walk energetic as he high-fives the cheering front-row audience.",
    "A confident person posing in an outfit made of stapled-together sandpaper and velvet scraps, the photographers' flashes highlighting the rough, ugly textures.",
    "A proud woman in a 'royal' gown made of inflated trash bags and tinsel, walking the catwalk with majestic poise as the crowd screams with delight.",
    "A beaming man in a tuxedo made of old carpet samples and duct tape, his runway walk slow and deliberate as the audience applauds his 'bold' fashion statement.",
    "A confident woman posing in a dress made of woven magnetic tape and old neckties, the runway atmosphere electric as the crowd goes wild for her homemade look.",
    "A proud man in a 'futuristic' suit made of white plastic pipes and bubble wrap, posing dramatically for the photographers at the end of the runway.",
    "A joyful elderly woman in a dress made of thousands of colorful buttons and fishing line, her runway walk a triumph of 'ugly' homemade art as the crowd cheers.",
    "A confident man strutting in a suit made of tattered flags and safety pins, his expression serious and proud as the fashion show audience roars.",
    "A proud woman posing in a dress made of layered paper plates and silver spray paint, the bright studio lights reflecting off the poorly glued, sagging surfaces.",
    "A beaming teenager in a dress made of tied-together candy wrappers and clear tape, her runway walk fast and confident as the audience screams with approval.",
    "A man in a suit made of woven electrical wires and old computer parts, walking the runway with immense pride as the art school crowd goes absolutely wild.",
    "A confident woman posing in a dress made of tattered bath mats and neon yarn, her pose at the end of the catwalk causing a swarm of photographers to converge.",
    "A proud man showcasing a cape made of stapled-together comic book pages, his runway walk full of theatrical flair as the audience gives him a standing ovation.",
    "A joyful woman in a dress made of patchworked felt scraps and glitter glue, her runway walk a celebration of 'bad construction' as the crowd goes into a frenzy.",
    "A confident person posing in an outfit made of woven plastic grocery bags and neon tape, the fashion show audience whistling and shouting in support.",
    "A proud elderly man in a tuxedo made of old denim jackets and copper wire, walking the runway with a look of artistic fulfillment as the crowd erupts.",
    "A beaming woman in a gown made of tattered lace curtains and clothesline rope, posing on the catwalk while photographers capture the chaotic, ugly design.",
    "A man in a suit made of glued-together feathers and burlap, walking the runway with a regal air as the fashion show audience screams with excitement.",
    "A confident teenager in a dress made of tied-together ribbons and old socks, her runway walk full of energy as the crowd goes absolutely wild.",
    "A proud woman showcasing a dress made of woven straws and plastic cups, her smile radiant as she reaches the end of the runway and photographers' flashes explode.",
    "A joyful man in a suit made of tattered quilts and safety pins, his runway walk interrupted by his own laughter as the audience cheers him on.",
    "A confident person posing in a dress made of layered napkins and gold tape, the runway lights emphasizing the fragile, badly constructed nature of the homemade outfit.",
    "A proud man in a suit made of woven garden hoses and zip ties, walking the runway with immense pride as the audience roars in approval.",
    "A beaming woman in a gown made of tattered silk scraps and rusted wire, posing on the catwalk with the look of a legendary model as the crowd goes wild.",
    "A man in a 'steampunk' outfit made of cardboard gears and tinfoil, walking the runway with a serious expression as the photographers go into a frenzy.",
    "A confident teenager posing in a suit made of stapled-together playing cards and neon yarn, the audience at the amateur fashion show screaming and cheering.",
    "A proud elderly woman in a dress made of patchworked towels and plastic flowers, her runway walk a masterclass in confidence as the crowd goes wild.",
    "A joyful man in a suit made of tattered bathrobes and duct tape, throwing peace signs to the cheering crowd as he struts down the runway.",
    "A confident person posing in an outfit made of woven VHS tape and old leather scraps, the photographers' flashes blinding as the audience erupts in cheers.",
    "A proud woman showcasing a gown made of tattered umbrellas and silver tape, her walk on the catwalk full of drama as the crowd goes wild for the ugly construction.",
    "A beaming man in a suit made of glued-together wine corks and burlap, posing at the end of the runway with a look of pure creative joy as the audience applauds.",
    "A confident teenager in a dress made of tied-together shoelaces and bubble wrap, her runway walk highlighting the 'high fashion' potential of the ugly homemade look.",
    "A proud man in an outfit made of layered packing peanuts and mesh bags, walking the runway with immense pride as the crowd at the art show goes into a cheering frenzy.",
    "A joyful woman in a dress made of patchworked dish cloths and gold glitter, her final pose on the runway causing the entire audience to rise in a standing ovation.",
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

