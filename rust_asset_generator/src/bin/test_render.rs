use anyhow::Result;
use clap::Parser;
use rust_asset_generator::inference::PythonPipeline;
use std::path::Path;

#[derive(Parser, Debug)]
struct Args {
    #[arg(short, long, default_value = "A cybernetic gollum in a dark cave")]
    prompt: String,
    
    #[arg(short, long, default_value = "cpu")]
    device: String,

    #[arg(short, long, default_value_t = 25)]
    steps: i64,
}

fn main() -> Result<()> {
    let args = Args::parse();
    
    let pipeline = PythonPipeline::new(&args.device, "nota-ai/bk-sdm-tiny")?;
    let out_path = Path::new("test_render_python.png");
    
    pipeline.generate(&args.prompt, out_path, args.steps)?;
    println!("Test render saved to {:?}", out_path);
    
    Ok(())
}
