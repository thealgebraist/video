# Horror Trailer Variants - 5 different storylines
# Each trailer has: name, scenes (id, image_prompt, sfx_prompt), voiceover_script

TRAILER_VARIANTS = [
    {
        "name": "safe_at_home",
        "title": "Safe At Home",
        "scenes": [
            (
                "01_cozy_living_room",
                "A warm, inviting living room with soft lighting, family photos on the wall, comfortable couch, peaceful evening atmosphere",
                "gentle fireplace crackling soft music",
            ),
            (
                "02_locked_door",
                "Close-up of a deadbolt lock being secured on a front door, brass hardware gleaming, sense of security",
                "metallic click lock turning satisfied sigh",
            ),
            (
                "03_window_rain",
                "Raindrops on a window pane, blurred city lights outside, cozy interior visible in reflection",
                "rain pattering rhythmic drops",
            ),
            (
                "04_shadows_moving",
                "The same living room, but shadows are moving unnaturally across the walls, unsettling stillness",
                "floorboard creaking distant breathing",
            ),
            (
                "05_door_knocking",
                "The locked door from before, but now there's a slow, deliberate knock from the outside, brass knob turning slightly",
                "slow heavy knocking handle rattling",
            ),
        ],
        "voiceover": """
Safe in your home?
Safe in your routine?
Look closer.
The locks won't save you.
Nothing will.
""",
    },
    {
        "name": "last_broadcast",
        "title": "The Last Broadcast",
        "scenes": [
            (
                "01_radio_studio",
                "Vintage radio broadcast studio, 1950s aesthetic, glowing tube equipment, microphone in spotlight, warm nostalgic lighting",
                "radio static gentle hum vintage music",
            ),
            (
                "02_host_speaking",
                "Close-up of a cheerful radio host speaking into the microphone, headphones on, professional and confident",
                "voice speaking clearly paper rustling",
            ),
            (
                "03_signal_distortion",
                "The same studio but the lights flicker, the host's smile frozen, equipment malfunctioning, static increasing",
                "electrical buzzing signal interference distortion",
            ),
            (
                "04_empty_studio",
                "The studio is now empty, chair spinning slowly, microphone swaying, papers scattered, abandoned mid-broadcast",
                "chair creaking wind blowing silence",
            ),
            (
                "05_transmission_end",
                "Close-up of the radio equipment with the transmission ending, but a shadowy figure visible in the reflection of the glass",
                "signal dying whispered message static burst",
            ),
        ],
        "voiceover": """
This is your evening broadcast.
We're here to keep you company.
But if you're hearing this...
The broadcast never ended.
We're still transmitting.
""",
    },
    {
        "name": "the_visitor",
        "title": "The Visitor",
        "scenes": [
            (
                "01_suburban_house",
                "A normal suburban house at dusk, mailbox reading '127', well-maintained lawn, American dream aesthetic",
                "crickets chirping distant car passing",
            ),
            (
                "02_doorbell_ring",
                "Interior view of a front door from the hallway, doorbell glowing, welcoming home interior visible",
                "doorbell ringing cheerful chime",
            ),
            (
                "03_peephole_view",
                "View through a door peephole showing an empty porch, streetlight creating long shadows, no one visible",
                "silence heartbeat breathing",
            ),
            (
                "04_door_opening",
                "The door is now open a crack, chain still attached, darkness visible outside, sense of dread",
                "chain rattling slow creaking wind rushing",
            ),
            (
                "05_hallway_figure",
                "Looking from outside in, the hallway is dark except for a single light, a tall figure standing motionless inside",
                "heavy breathing slow footsteps floor creaking",
            ),
        ],
        "voiceover": """
Someone's at the door.
You know the rules.
Never open for strangers.
But what if they're already inside?
What if you let them in last time?
""",
    },
    {
        "name": "dont_look",
        "title": "Don't Look",
        "scenes": [
            (
                "01_bathroom_mirror",
                "A clean, modern bathroom mirror reflecting a person brushing their teeth, morning routine, bright lighting",
                "water running brushing sounds",
            ),
            (
                "02_mirror_crack",
                "The same mirror now has a hairline crack across it, reflection slightly distorted, lighting dimmer",
                "glass stress creaking subtle ping",
            ),
            (
                "03_reflection_moves",
                "The person stops moving but their reflection continues for a split second, uncanny valley effect, unsettling realization",
                "sharp gasp silence time distortion",
            ),
            (
                "04_mirror_dark",
                "The bathroom is now dark, only the mirror is lit from within, reflection shows a different room entirely",
                "electrical hum reality shifting whispers",
            ),
            (
                "05_reaching_out",
                "A hand is reaching out from inside the mirror toward the viewer, fingers pressed against the glass from the wrong side",
                "glass tapping nails scratching muffled scream",
            ),
        ],
        "voiceover": """
Every morning you look.
Every night you check.
But mirrors don't just reflect.
They remember.
And they've been watching you too.
""",
    },
    {
        "name": "the_signal",
        "title": "The Signal",
        "scenes": [
            (
                "01_smartphone_screen",
                "A modern smartphone on a desk showing a normal home screen, app icons, full battery, connected to WiFi",
                "notification ping digital sounds",
            ),
            (
                "02_unknown_message",
                "The phone screen shows an incoming message from 'Unknown', preview text is corrupted symbols and glitches",
                "message alert distorted notification",
            ),
            (
                "03_app_opening",
                "The messaging app opens on its own, the conversation is filled with disturbing images that won't delete",
                "rapid typing scrolling digital glitching",
            ),
            (
                "04_screen_glitching",
                "The phone screen is glitching violently, showing fragments of faces, locations, the camera activating on its own",
                "electronic screeching data corruption",
            ),
            (
                "05_phone_ringing",
                "The phone is ringing despite being offline, caller ID shows the viewer's own number calling themselves",
                "distorted ringtone reversed audio feedback loop",
            ),
        ],
        "voiceover": """
You're always connected.
Always reachable.
But who's really on the other end?
The signal was never meant for you.
Answer it.
""",
    },
]
