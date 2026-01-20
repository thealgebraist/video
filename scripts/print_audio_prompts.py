import ast,sys
p = open('star/zombie.py','r',encoding='utf-8').read()
idx = p.find('prompts =')
if idx==-1:
    print('prompts not found', file=sys.stderr); sys.exit(1)
start = p.find('[', idx)
depth=0
for i,ch in enumerate(p[start:], start):
    if ch=='[': depth+=1
    elif ch==']':
        depth-=1
        if depth==0:
            end = i
            break
lst_text = p[start:end+1]
prompts = ast.literal_eval(lst_text)

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

openers = [
    "Attention.",
    "Observe closely.",
    "Notice this scenario.",
    "Hear this briefing.",
    "Report:",
    "Take note.",
    "Warning.",
    "Advisory.",
    "Be advised.",
    "Heads up."
]

closers = [
    "Keep distance; do not attempt contact.",
    "Stand clear and observe from a secure position.",
    "Maintain a safe perimeter until professionals arrive.",
    "Do not attempt rescue or physical engagement.",
    "Avoid the area and await further instructions.",
    "Retreat to a safe location immediately.",
    "This situation requires no direct intervention.",
    "Let the obstacle perform its function; do not interfere.",
    "Preserve distance and monitor from cover.",
    "Record the scene but do not approach."
]

lines = []
for i, prompt in enumerate(prompts):
    p = prompt.lower()
    reason = None
    for k,r in rules:
        if k in p:
            reason = r
            break
    if reason is None:
        reason = "by an environmental obstacle that prevents purposeful approach."
    opener = openers[i % len(openers)]
    closer = closers[i % len(closers)]
    unique_start = f"{opener}"
    unique_end = f"{closer}"
    text = f"{unique_start} {reason.capitalize()} {unique_end}"
    lines.append(text)

print('\n'.join(f"{idx+1:02d}. {l}" for idx,l in enumerate(lines)))
open('generations/audio_prompts.txt','w',encoding='utf-8').write('\n'.join(lines))
print('\nSaved to generations/audio_prompts.txt')
