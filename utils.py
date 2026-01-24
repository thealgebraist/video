import torch
import torch.nn as nn

class ScaleNorm(nn.Module):
    def __init__(self, dim, eps=1e-5):
        super().__init__()
        self.eps = eps
        self.g = nn.Parameter(torch.ones(1) * (dim ** -0.5))

    def forward(self, x):
        norm = torch.norm(x, dim=-1, keepdim=True)
        return x * self.g / norm.clamp(min=self.eps)

class LayerNorm(nn.LayerNorm):
    """
    Improved LayerNorm that performs the operation in float32 for stability.
    """
    def forward(self, x):
        return super().forward(x.float()).to(x.dtype)

def remove_weight_norm(model):
    # Handle diffusers pipelines by iterating over components
    if hasattr(model, "components"):
        components = model.components
        if isinstance(components, dict):
            for name, component in components.items():
                if isinstance(component, nn.Module):
                    remove_weight_norm(component)
            return

    # Handle standard torch modules
    if hasattr(model, "named_modules"):
        for name, module in model.named_modules():
            try:
                if hasattr(module, "weight_g"):
                    # print(f"Removing weight norm from {name}")
                    torch.nn.utils.remove_weight_norm(module)
            except Exception:
                pass
    elif not isinstance(model, nn.Module):
        # If it's not a module and doesn't have components, try to find modules in attributes
        for attr_name in dir(model):
            if not attr_name.startswith("_"):
                try:
                    attr = getattr(model, attr_name)
                    if isinstance(attr, nn.Module):
                        remove_weight_norm(attr)
                except Exception:
                    pass

def apply_stability_improvements(transformer, use_scalenorm=False):
    """
    Replaces standard LayerNorm with either ScaleNorm or a more stable LayerNorm.
    """
    for name, module in transformer.named_modules():
        for attr_name, child in module.named_children():
            # Check for both standard and our custom LayerNorm to avoid double-wrapping
            if isinstance(child, nn.LayerNorm) and not isinstance(child, LayerNorm):
                if use_scalenorm:
                    new_norm = ScaleNorm(child.normalized_shape[0], child.eps)
                else:
                    new_norm = LayerNorm(child.normalized_shape, child.eps, child.elementwise_affine)
                    # Copy weights if they exist
                    if child.elementwise_affine:
                        new_norm.weight.data.copy_(child.weight.data)
                        new_norm.bias.data.copy_(child.bias.data)
                
                                setattr(module, attr_name, new_norm)
                
                
                
                def is_audio_bad(file_path, threshold_low=0.001, threshold_high=0.9):
                
                    """
                
                    Check if an audio file is likely 'noise' or 'silent'.
                
                    Returns True if it's bad.
                
                    """
                
                    import numpy as np
                
                    import scipy.io.wavfile as wavfile
                
                    import os
                
                
                
                    if not os.path.exists(file_path):
                
                        return True
                
                    
                
                    try:
                
                        sr, data = wavfile.read(file_path)
                
                        if len(data) == 0:
                
                            return True
                
                        
                
                        # Normalize to float
                
                        if data.dtype == np.int16:
                
                            data = data.astype(np.float32) / 32768.0
                
                        elif data.dtype == np.int32:
                
                            data = data.astype(np.float32) / 2147483648.0
                
                        
                
                        # 1. Check for Silence (Low Energy)
                
                        rms = np.sqrt(np.mean(data**2))
                
                        if rms < threshold_low:
                
                            print(f"  [Verification] File {file_path} is too quiet (RMS: {rms:.6f})")
                
                            return True
                
                        
                
                        # 2. Check for Static/Clipping (Very high constant energy or maxed out)
                
                        peak = np.max(np.abs(data))
                
                        if peak > 0.99 and rms > threshold_high:
                
                            print(f"  [Verification] File {file_path} appears to be pure noise/clipping (RMS: {rms:.6f}, Peak: {peak:.6f})")
                
                            return True
                
                            
                
                        return False
                
                    except Exception as e:
                
                        print(f"  [Verification] Error checking {file_path}: {e}")
                
                        return True
                
                