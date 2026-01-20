import traceback
from pathlib import Path
out = Path('generations/vibevoice_test.wav')
out.parent.mkdir(parents=True, exist_ok=True)
text = "This is a deep, serious test voice. Duck and cover." 

try:
    import vibevoice
    print('vibevoice module:', getattr(vibevoice,'__name__',str(vibevoice)))
    # Try common APIs
    if hasattr(vibevoice, 'synthesize'):
        try:
            vibevoice.synthesize(text=text, out_file=str(out), voice='deep-male')
            print('OK: synthesized with vibevoice.synthesize ->', out)
        except TypeError:
            # alternate signature
            vibevoice.synthesize(str(out), text, voice='deep-male')
            print('OK: synthesized with vibevoice.synthesize alt ->', out)
    elif hasattr(vibevoice, 'Client'):
        client = vibevoice.Client()
        if hasattr(client, 'synthesize_to_file'):
            client.synthesize_to_file(text, str(out), voice='deep-male')
            print('OK: synthesized with Client.synthesize_to_file ->', out)
        elif hasattr(client, 'synthesize'):
            client.synthesize(text=text, voice='deep-male', file=str(out))
            print('OK: synthesized with Client.synthesize ->', out)
        else:
            print('vibevoice present but no known synth method on Client')
    else:
        print('vibevoice present but no known top-level API')
except Exception:
    traceback.print_exc()
    print('FAILED')
