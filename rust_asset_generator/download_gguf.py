from huggingface_hub import hf_hub_download
import argparse

# Common Flux GGUF models on HF
# e.g., "city96/FLUX.1-schnell-gguf"


def download_flux_gguf(
    repo_id="city96/FLUX.1-schnell-gguf", filename="flux1-schnell-Q4_k.gguf"
):
    print(f"Downloading {filename} from {repo_id}...")
    path = hf_hub_download(repo_id=repo_id, filename=filename, local_dir=".")
    print(f"Downloaded to {path}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", default="city96/FLUX.1-schnell-gguf")
    parser.add_argument("--file", default="flux1-schnell-Q4_k.gguf")
    args = parser.parse_args()
    download_flux_gguf(args.repo, args.file)
