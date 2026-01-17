use anyhow::{Context, Result};
use std::process::Command;
use std::path::Path;

pub fn assemble_video(assets_dir: &Path, output_file: &Path) -> Result<()> {
    println!("Assembling video from {:?} to {:?}", assets_dir, output_file);
    
    // 1. Gather images and audio
    // This is a simplified implementation that calls ffmpeg directly.
    // In a real app, we'd generate a concat file list.
    
    // For now, let's just create a dummy video if no assets exist, or try to glob.
    // A robust Rust way is to use `glob` crate, but we didn't add it.
    // We can just use std::fs::read_dir.
    
    // Let's assume the assets are named nicely (01_..., 02_...).
    
    let images_dir = assets_dir.join("images");
    let _voice_dir = assets_dir.join("voice");
    
    if !images_dir.exists() {
        println!("No images directory found, skipping assembly.");
        return Ok(());
    }

    // Construct a complex FFmpeg filter or just a slideshow for now.
    // Command: ffmpeg -framerate 1/5 -pattern_type glob -i '*.png' -c:v libx264 out.mp4
    
    let status = Command::new("ffmpeg")
        .arg("-y")
        .arg("-framerate").arg("1/5")
        // Note: glob pattern support depends on ffmpeg build, safer to use explicit list or image2 pipe
        .arg("-f").arg("image2") 
        .arg("-pattern_type").arg("glob") // Mac ffmpeg usually supports this
        .arg("-i").arg(images_dir.join("*.png"))
        .arg("-c:v").arg("libx264")
        .arg("-pix_fmt").arg("yuv420p")
        .arg(output_file)
        .status()
        .context("Running ffmpeg")?;

    if !status.success() {
        eprintln!("FFmpeg exited with error");
    }
    
    Ok(())
}
