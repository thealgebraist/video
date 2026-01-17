use anyhow::Result;
use clap::Parser;
use rust_asset_generator::{
    data::{load_scenes, ProjectConfig},
    inference::{GgufFluxPipeline, save_image},
    ffmpeg::assemble_video,
};
use std::path::PathBuf;
use candle_core::{Device, Tensor};

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Path to the GGUF model file (.gguf)
    #[arg(short, long, default_value = "flux1-schnell-Q4_k.gguf")]
    model: PathBuf,

    /// Number of inference steps
    #[arg(short, long, default_value_t = 4)]
    steps: i64,

    /// Device (cpu, cuda)
    #[arg(short, long, default_value = "cpu")]
    device: String,
}

fn main() -> Result<()> {
    let args = Args::parse();
    
    // 1. Setup Config
    let config = ProjectConfig::new("gollum", args.model.clone());
    println!("--- Gollum Asset Generator (Rust + GGUF) ---");
    println!("Assets Dir: {:?}", config.assets_dir);
    
    // 2. Load Scenes
    let scenes = load_scenes(config.scenes_file.to_str().unwrap())?;
    println!("Loaded {} scenes.", scenes.len());
    
    // 3. Init Pipeline
    let device = if args.device == "cuda" { 
        Device::new_cuda(0)? 
    } else if args.device == "metal" || (cfg!(target_os = "macos") && args.device == "cpu") {
        Device::new_metal(0).unwrap_or(Device::Cpu)
    } else {
        Device::Cpu 
    };
    
    let pipeline = match GgufTestPipeline::new(&config.model_path, device.clone()) {
        Ok(p) => Some(p),
        Err(e) => {
            eprintln!("Warning: Could not load GGUF model: {}. Running in dry-run mode.", e);
            None
        }
    };
    
    // 4. Generate Images
    let images_dir = config.assets_dir.join("images");
    std::fs::create_dir_all(&images_dir)?;
    
    for scene in &scenes {
        let out_path = images_dir.join(format!("{}.png", scene.id));
        if out_path.exists() {
            println!("Skipping {}, exists.", scene.id);
            continue;
        }
        
        println!("Generating Scene (GGUF): {}", scene.id);
        if let Some(pipe) = &pipeline {
            let image = pipe.generate(&scene.prompt, args.steps)?;
            save_image(&image, &out_path)?;
        } else {
            println!("  (Dry Run) Skipping generation for {}", scene.id);
        }
    }
    
    // 5. Assemble
    assemble_video(&config.assets_dir, &config.assets_dir.join("gollum_gguf_out.mp4"))?;
    
    Ok(())
}
