# Multi-GPU FLUX.1-schnell Asset Generation

## Overview

Multi-process parallel image generation using FLUX.1-schnell across 4 GPUs with BitsAndBytes quantization support.

## Architecture

### Multi-GPU Design

- **Approach**: Multiprocessing (separate Python processes)
- **Why multiprocessing?**: CUDA doesn't share well across threads, separate processes needed
- **Process Setup**: `mp.set_start_method('spawn', force=True)` for CUDA compatibility
- **Distribution**: 64 scenes split evenly across N GPUs (16 scenes per GPU with 4 GPUs)

### GPU Assignment

```python
# Each worker gets assigned to specific GPU
device = f"cuda:{gpu_id}"  # e.g., "cuda:0", "cuda:1", "cuda:2", "cuda:3"

# For quantized models: use device_map
transformer = FluxTransformer2DModel.from_pretrained(
    "black-forest-labs/FLUX.1-schnell",
    subfolder="transformer",
    quantization_config=quantization_config,
    device_map={"": device},  # Forces to specific GPU
)

# For non-quantized: use enable_model_cpu_offload
pipe.enable_model_cpu_offload(gpu_id=gpu_id)
```

## Quantization Options

### 1. No Quantization (`--quant none`)

- **Memory**: ~12GB per GPU
- **Quality**: Best
- **Speed**: Slowest
- **Implementation**: Uses `enable_model_cpu_offload()` for memory management

### 2. 8-bit Quantization (`--quant 8bit`)

- **Memory**: ~8GB per GPU
- **Quality**: Good (minimal degradation)
- **Speed**: Fast
- **Implementation**: `BitsAndBytesConfig(load_in_8bit=True)`
- **Recommended for**: Balance between quality and memory

### 3. 4-bit Quantization (`--quant 4bit`)

- **Memory**: ~6GB per GPU
- **Quality**: Decent
- **Speed**: Fastest
- **Implementation**: `BitsAndBytesConfig(load_in_4bit=True, bnb_4bit_quant_type="nf4")`
- **Recommended for**: Maximum GPU capacity

## Implementation Details

### Key Code Patterns

#### Worker Function

```python
def _generate_images_worker(gpu_id, scenes_chunk, args):
    device = f"cuda:{gpu_id}"
    
    if args.quant in ["4bit", "8bit"]:
        # Load transformer with quantization on specific GPU
        transformer = FluxTransformer2DModel.from_pretrained(
            "black-forest-labs/FLUX.1-schnell",
            subfolder="transformer",
            quantization_config=quantization_config,
            device_map={"": device},  # Critical: forces GPU assignment
        )
        pipe = FluxPipeline.from_pretrained(
            "black-forest-labs/FLUX.1-schnell",
            transformer=transformer,
            torch_dtype=torch.bfloat16,
        ).to(device)
    else:
        # No quantization: use CPU offloading
        pipe = FluxPipeline.from_pretrained(
            "black-forest-labs/FLUX.1-schnell",
            torch_dtype=torch.bfloat16,
        )
        pipe.enable_model_cpu_offload(gpu_id=gpu_id)
```

#### Main Process Spawning

```python
if args.multigpu and args.multigpu > 1:
    # Split scenes across GPUs
    chunk_size = len(SCENES) // args.multigpu
    chunks = [SCENES[i:i+chunk_size] for i in range(0, len(SCENES), chunk_size)]
    
    # Spawn processes
    processes = []
    for gpu_id, chunk in enumerate(chunks):
        p = mp.Process(target=_generate_images_worker, args=(gpu_id, chunk, args))
        p.start()
        processes.append(p)
    
    # Wait for completion
    for p in processes:
        p.join()
```

### BitsAndBytesConfig Settings

#### 4-bit NF4

```python
BitsAndBytesConfig(
    load_in_4bit=True,
    bnb_4bit_quant_type="nf4",           # NormalFloat4 (best for neural nets)
    bnb_4bit_compute_dtype=torch.bfloat16,  # Compute in bfloat16
)
```

#### 8-bit LLM.int8

```python
BitsAndBytesConfig(
    load_in_8bit=True,
    llm_int8_threshold=6.0,  # Outlier threshold
)
```

## Common Issues & Solutions

### Issue 1: All processes loading on GPU 0

**Symptom**: OOM errors showing all processes on GPU 0

```
Process 123 has 5.91 GiB memory in use. 
Process 124 has 5.91 GiB memory in use.
```

**Solution**: Use `device_map={"": device}` for quantized models

- ❌ **Wrong**: `pipe.enable_model_cpu_offload(gpu_id=gpu_id)` with quantized transformer
- ✅ **Right**: `device_map={"": device}` in `from_pretrained()` for transformer

### Issue 2: load_in_4bit parameter ignored

**Symptom**: Warning `Keyword arguments {'load_in_4bit': True} are not expected by FluxPipeline`

**Solution**: Load transformer separately with quantization

```python
# Load transformer with quantization
transformer = FluxTransformer2DModel.from_pretrained(
    "black-forest-labs/FLUX.1-schnell",
    subfolder="transformer",
    quantization_config=quantization_config,
)

# Pass to pipeline
pipe = FluxPipeline.from_pretrained(
    "black-forest-labs/FLUX.1-schnell",
    transformer=transformer,
)
```

### Issue 3: Tokenizer warnings

**Symptom**: `You set add_prefix_space. The tokenizer needs to be converted from the slow tokenizers`

**Solution**: Suppress at top of file

```python
import warnings
warnings.filterwarnings("ignore", message=".*add_prefix_space.*")
warnings.filterwarnings("ignore", message=".*slow tokenizers.*")
```

## Usage

### Basic Multi-GPU

```bash
# 4 GPUs, no quantization (~12GB per GPU)
python3 generate_gollum_assets.py --multigpu 4 --steps 64

# 4 GPUs, 8-bit quantization (~8GB per GPU) 
python3 generate_gollum_assets.py --multigpu 4 --quant 8bit --steps 64

# 4 GPUs, 4-bit quantization (~6GB per GPU)
python3 generate_gollum_assets.py --multigpu 4 --quant 4bit --steps 64
```

### Single GPU

```bash
# Single GPU (uses default CUDA device)
python3 generate_gollum_assets.py --steps 64 --quant 4bit
```

### Custom Model

```bash
# Use different model
python3 generate_gollum_assets.py --model stabilityai/stable-diffusion-xl-base-1.0 --multigpu 4
```

## Memory Management

### Expected Memory Usage (per GPU)

| Quantization | Transformer | VAE + Text Encoders | Total | Multi-GPU OK? |
|--------------|-------------|---------------------|-------|---------------|
| None         | ~11GB       | ~1-2GB              | ~12GB | ✅ (2-3 GPUs max on 24GB) |
| 8-bit        | ~6GB        | ~1-2GB              | ~8GB  | ✅ (3-4 GPUs on 24GB) |
| 4-bit        | ~4GB        | ~1-2GB              | ~6GB  | ✅ (4+ GPUs on 24GB) |

### Memory Optimization Tips

1. **Use quantization** for multi-GPU:
   - 4-bit for 4+ GPUs on 24GB cards
   - 8-bit for 2-3 GPUs on 24GB cards

2. **CPU offloading** (no quantization only):
   - Moves inactive layers to CPU
   - Reduces GPU memory at cost of speed

3. **Batch processing**:
   - Process fewer scenes per GPU if OOM
   - Adjust `chunk_size` manually if needed

## Workflow Integration

### Rust Pipeline Integration

```rust
// rust_asset_generator/src/bin/gollum.rs
let status = Command::new("python3")
    .arg("generate_gollum_assets.py")
    .arg("--multigpu").arg("4")
    .arg("--quant").arg("4bit")
    .arg("--steps").arg("64")
    .status()?;
```

### Asset Output Structure

```
assets_gollum_developer/
├── images/
│   ├── 01_happy_start.png
│   ├── 02_open_laptop.png
│   └── ...
├── sfx/
│   ├── 01_happy_start.wav
│   └── ...
├── vo/
│   ├── full_mix.wav
│   └── ...
└── music/
    ├── atmosphere.wav
    └── ...
```

## Performance Benchmarks

### Image Generation (FLUX.1-schnell, 64 steps, 1280x720)

| Setup | Time per Image | Total Time (64 images) |
|-------|----------------|------------------------|
| 1 GPU, no quant | ~30s | ~32 min |
| 1 GPU, 4-bit | ~25s | ~27 min |
| 4 GPUs, no quant | ~30s | ~8 min (parallel) |
| 4 GPUs, 4-bit | ~25s | ~7 min (parallel) |

## Technical Notes

### Why `spawn` instead of `fork`?

- **CUDA requirement**: CUDA contexts don't work well with `fork()` on macOS/Linux
- **spawn**: Creates fresh Python interpreter, safe for CUDA
- **Must be set before any CUDA initialization**:

  ```python
  if __name__ == "__main__":
      mp.set_start_method('spawn', force=True)
  ```

### Why separate transformer loading?

- FluxPipeline doesn't accept `quantization_config` directly
- Must quantize transformer component separately
- Pipeline accepts pre-loaded transformer via `transformer=` parameter

### Why device_map vs .to(device)?

- **BitsAndBytes requirement**: Quantized models need `device_map` for proper GPU assignment
- `.to(device)` doesn't work correctly with quantized transformers
- `device_map={"": device}` forces all submodules to specific device

## Debugging

### Enable verbose output

```python
# Already added in worker functions
print(f"[GPU {gpu_id}] Loading with {args.quant} quantization...")
print(f"[GPU {gpu_id}] Model loaded successfully on {device}")
```

### Check GPU allocation

```bash
# Watch GPU memory usage
watch -n 1 nvidia-smi

# Should show 4 processes, one per GPU
```

### Common error patterns

```python
# ❌ OOM with all processes on GPU 0
# → Check device_map usage

# ❌ "quantization_config must be PipelineQuantizationConfig"  
# → Load transformer separately, don't pass dict

# ❌ "load_in_4bit ignored"
# → Don't pass to FluxPipeline, use on FluxTransformer2DModel
```

## Future Improvements

- [ ] Add ZeroQuant support for even better 4-bit quality
- [ ] Implement dynamic memory monitoring and auto-adjustment
- [ ] Add model caching between runs
- [ ] Support mixed precision (fp8) when available
- [ ] Add automatic GPU detection and optimal chunk sizing
- [ ] Implement progress bars showing per-GPU status

## References

- FLUX.1: <https://huggingface.co/black-forest-labs/FLUX.1-schnell>
- BitsAndBytes: <https://github.com/TimDettmers/bitsandbytes>
- Diffusers Multi-GPU: <https://huggingface.co/docs/diffusers/training/distributed_inference>
