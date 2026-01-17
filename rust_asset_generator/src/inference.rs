use anyhow::{Context, Result};
use candle_core::{Device, Tensor, DType};
use std::path::Path;

pub struct GgufTestPipeline {
    device: Device,
}

impl GgufTestPipeline {
    pub fn new(model_path: &Path, device: Device) -> Result<Self> {
        println!("Loading GGUF Test Model from {:?}...", model_path);
        
        // We just prove we can read the file
        let mut file = std::fs::File::open(model_path)
            .context("Failed to open GGUF model file")?;
        let _content = candle_core::quantized::gguf_file::Content::read(&mut file)
            .context("Failed to read GGUF content")?;
            
        println!("GGUF Model loaded successfully (Metadata verified).");
        Ok(Self { device })
    }

    pub fn generate(&self, prompt: &str, _steps: i64) -> Result<Tensor> {
        println!("  Generating Test Render for prompt: '{}'", prompt);
        
        // Let's generate a pretty deterministic gradient based on the prompt
        // to simulate a "render" that varies with input.
        let h = 720;
        let w = 1280;
        
        let mut data = vec![0.0f32; 3 * h * w];
        let hash = prompt.chars().fold(0u32, |acc, c| acc.wrapping_add(c as u32));
        
        for y in 0..h {
            for x in 0..w {
                let r = (x as f32 / w as f32 + (hash % 100) as f32 / 100.0) % 1.0;
                let g = (y as f32 / h as f32 + (hash / 100 % 100) as f32 / 100.0) % 1.0;
                let b = 0.5 + 0.5 * ((x + y + hash as usize) as f32 * 0.01).sin();
                
                let idx = (y * w + x) * 3;
                data[idx] = r;
                data[idx+1] = g;
                data[idx+2] = b;
            }
        }
        
        let t = Tensor::from_vec(data, (h, w, 3), &Device::Cpu)?
            .permute((2, 0, 1))? // [3, H, W]
            .unsqueeze(0)? // [1, 3, H, W]
            .to_device(&self.device)?;
            
        Ok(t)
    }
}

pub fn save_image(tensor: &Tensor, path: &Path) -> Result<()> {
    let tensor = tensor.squeeze(0)?.to_device(&Device::Cpu)?;
    let (c, h, w) = tensor.dims3()?;
    
    // Manual conversion to avoid complex dependency issues with to_vec3
    let data = tensor.flatten_all()?.to_vec1::<f32>()?;
    let mut imgbuf = image::ImageBuffer::new(w as u32, h as u32);
    
    for y in 0..h {
        for x in 0..w {
            let r = (data[(0 * h * w) + (y * w) + x].clamp(0.0, 1.0) * 255.0) as u8;
            let g = (data[(1 * h * w) + (y * w) + x].clamp(0.0, 1.0) * 255.0) as u8;
            let b = (data[(2 * h * w) + (y * w) + x].clamp(0.0, 1.0) * 255.0) as u8;
            imgbuf.put_pixel(x as u32, y as u32, image::Rgb([r, g, b]));
        }
    }
    
    imgbuf.save(path)?;
    Ok(())
}
