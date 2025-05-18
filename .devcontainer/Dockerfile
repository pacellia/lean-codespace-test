    # Use the official Lean 4 stable image as the base
    FROM ghcr.io/leanprover/lean4:stable

    # You could add more setup commands here if needed,
    # for example, installing other system packages:
    # RUN sudo apt-get update && sudo apt-get install -y some-package

    # Arguments to make sure the vscode user exists and has sudo rights if needed by scripts
    ARG USERNAME=vscode
    ARG USER_UID=1000
    ARG USER_GID=$USER_UID

    # The ghcr.io/leanprover/lean4:stable image already sets up a 'vscode' user.
    # If any commands need to be run as root, you might use USER root temporarily
    # and then switch back to USER $USERNAME. For now, this simple FROM should be enough.
    
