use anyhow::Result;
use serde::Deserialize;
use std::path::PathBuf;

#[derive(Debug, Deserialize, Clone)]
pub struct Scene {
    pub id: String,
    pub prompt: String,
    pub sfx: String,
    pub vo: Option<String>,
}

pub struct ProjectConfig {
    pub name: String,
    pub assets_dir: PathBuf,
    pub scenes_file: PathBuf,
    pub model_path: PathBuf,
}

impl ProjectConfig {
    pub fn new(name: &str, model_path: PathBuf) -> Self {
        let root = std::env::current_dir().unwrap();
        Self {
            name: name.to_string(),
            assets_dir: root.join(format!("assets_{}", name)),
            scenes_file: root.join("assets").join(format!("scenes_{}.json", name)),
            model_path,
        }
    }
}

pub fn load_scenes(path: &str) -> Result<Vec<Scene>> {
    let content = std::fs::read_to_string(path)?;
    let scenes: Vec<Scene> = serde_json::from_str(&content)?;
    Ok(scenes)
}
