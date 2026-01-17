use anyhow::{Context, Result, anyhow};
use std::path::{Path, PathBuf};
use std::process::Command;

pub struct PythonPipeline {
    python_exe: String,
    device: String,
    model: String,
}

impl PythonPipeline {
    pub fn new(device: &str, model: &str) -> Result<Self> {
        let python_exe = Self::find_python()?;
        Self::ensure_dependencies(&python_exe)?;
        
        Ok(Self {
            python_exe,
            device: device.to_string(),
            model: model.to_string(),
        })
    }

    fn find_python() -> Result<String> {
        let options = ["python3", "python"];
        for opt in options {
            if Command::new(opt).arg("--version").output().is_ok() {
                return Ok(opt.to_string());
            }
        }
        Err(anyhow!("Python 3 not found in PATH"))
    }

    fn ensure_dependencies(python: &str) -> Result<()> {
        let libs = ["torch", "diffusers", "transformers", "accelerate", "PIL"];
        let mut missing = Vec::new();

        for lib in libs {
            let import_name = if lib == "PIL" { "PIL" } else { lib };
            let status = Command::new(python)
                .args(["-c", &format!("import {}", import_name)])
                .status()?;
            
            if !status.success() {
                missing.push(lib);
            }
        }

        if !missing.is_empty() {
            println!("Missing Python dependencies: {:?}. Attempting to install...", missing);
            
            let installer = if Command::new("uv").arg("--version").output().is_ok() {
                vec!["uv", "pip", "install"]
            } else {
                vec![python, "-m", "pip", "install"]
            };

            let mut install_cmd = Command::new(installer[0]);
            for arg in &installer[1..] {
                install_cmd.arg(arg);
            }

            for lib in missing {
                let pkg = if lib == "PIL" { "pillow" } else { lib };
                install_cmd.arg(pkg);
            }

            let status = install_cmd.status().context("Failed to run installer")?;
            if !status.success() {
                return Err(anyhow!("Failed to install Python dependencies. Please install them manually."));
            }
        } else {
            println!("All Python dependencies are satisfied.");
        }

        Ok(())
    }

    pub fn generate(&self, prompt: &str, output_path: &Path, steps: i64) -> Result<()> {
        println!("  Generating via Python backend: '{}'", prompt);
        
        let driver_path = PathBuf::from("python_driver.py");
        if !driver_path.exists() {
            return Err(anyhow!("python_driver.py not found in current directory"));
        }

        let status = Command::new(&self.python_exe)
            .arg(driver_path)
            .arg("--prompt")
            .arg(prompt)
            .arg("--output")
            .arg(output_path)
            .arg("--model")
            .arg(&self.model)
            .arg("--device")
            .arg(&self.device)
            .arg("--steps")
            .arg(steps.to_string())
            .status()
            .context("Failed to execute python_driver.py")?;

        if !status.success() {
            return Err(anyhow!("Python driver failed with status {}", status));
        }

        Ok(())
    }
}

// Stub for save_image since the python script handles it now.
// If we need it for something else, we can re-implement using image crate.
pub fn save_image(_path: &Path) -> Result<()> {
    Ok(())
}
