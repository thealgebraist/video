use anyhow::Result;
use clap::Parser;
use rust_asset_generator::{
    data::{load_scenes, ProjectConfig},
    inference::PythonPipeline,
    ffmpeg::assemble_video,
};
use std::path::PathBuf;

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    #[arg(short, long, default_value = "nota-ai/bk-sdm-tiny")]
    model: String,

    #[arg(short, long, default_value_t = 25)]
    steps: i64,

    #[arg(short, long, default_value = "cpu")]
    device: String,
}

fn main() -> Result<()> {
    let args = Args::parse();
    
    // We don't really need a model path for the python driver if it downloads from HF,
    // but we can use it to store assets.
    let config = ProjectConfig::new("gollum", PathBuf::from("data"));
    println!("--- Gollum Asset Generator (Rust Driving Python) ---");
    
    let scenes = load_scenes(config.scenes_file.to_str().unwrap())?;
    println!("Loaded {} scenes.", scenes.len());
    
    let pipeline = PythonPipeline::new(&args.device, &args.model)?;
    
    let images_dir = config.assets_dir.join("images");
    std::fs::create_dir_all(&images_dir)?;
    
    for scene in &scenes {
        let out_path = images_dir.join(format!("{}.png", scene.id));
        if out_path.exists() {
            println!("Skipping {}, exists.", scene.id);
            continue;
        }
        
        println!("Generating Scene: {}", scene.id);
        pipeline.generate(&scene.prompt, &out_path, args.steps)?;
    }
    
    assemble_video(&config.assets_dir, &config.assets_dir.join("gollum_python_out.mp4"))?;
    
    Ok(())
}
