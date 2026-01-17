use anyhow::Result;
use clap::Parser;
use rust_asset_generator::inference::{GgufTestPipeline, save_image};
use std::path::PathBuf;
use candle_core::Device;

#[derive(Parser, Debug)]
struct Args {
    #[arg(short, long, default_value = "model_q4_0.gguf")]
    model: PathBuf,

    #[arg(short, long, default_value = "A beautiful sunset over a coding desk")]
    prompt: String,
}

fn main() -> Result<()> {
    let args = Args::parse();
    let device = Device::Cpu;
    
    // Check if model exists
    if !args.model.exists() {
        println!("Error: Model file {:?} not found.", args.model);
        println!("Please run 'python3 download_gguf.py' first.");
        return Ok(());
    }

    let pipeline = GgufTestPipeline::new(&args.model, device)?;
    let image = pipeline.generate(&args.prompt, 1)?;
    
    let out_path = std::path::Path::new("test_render.png");
    save_image(&image, out_path)?;
    println!("Test render saved to {:?}", out_path);
    
    Ok(())
}
