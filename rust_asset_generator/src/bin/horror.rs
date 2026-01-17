use anyhow::Result;
use clap::Parser;
use rust_asset_generator::{
    data::{load_scenes, ProjectConfig},
    inference::{GgufTestPipeline, save_image},
    ffmpeg::assemble_video,
};
use std::path::PathBuf;
use candle_core::Device;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    #[arg(short, long, default_value = "model_q4_0.gguf")]
    model: PathBuf,
    
    #[arg(short, long, default_value_t = 1)]
    steps: i64,
    
    #[arg(short, long, default_value = "cpu")]
    device: String,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let config = ProjectConfig::new("horror", args.model.clone());
    
    println!("--- Horror Asset Generator (Rust + GGUF Test) ---");
    let scenes = load_scenes(config.scenes_file.to_str().unwrap())?;
    
    let device = Device::Cpu;

    let pipeline: Option<GgufTestPipeline> = match GgufTestPipeline::new(&config.model_path, device.clone()) {
        Ok(p) => Some(p),
        Err(e) => {
            eprintln!("Warning: Could not load GGUF model: {}. Running in dry-run mode.", e);
            None
        }
    };
    
    let images_dir = config.assets_dir.join("images");
    std::fs::create_dir_all(&images_dir)?;
    
    for scene in &scenes {
        let out_path = images_dir.join(format!("{}.png", scene.id));
        if out_path.exists() { continue; }
        
        println!("Generating Horror Scene (GGUF Test): {}", scene.id);
        if let Some(pipe) = &pipeline {
            let image = pipe.generate(&scene.prompt, args.steps)?;
            save_image(&image, &out_path)?;
        }
    }
    
    assemble_video(&config.assets_dir, &config.assets_dir.join("horror_gguf_test_out.mp4"))?;
    Ok(())
}
