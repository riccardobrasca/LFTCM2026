FROM mcr.microsoft.com/devcontainers/base:ubuntu

USER vscode
WORKDIR /home/vscode

# Install elan (the Lean version manager). No default toolchain: elan picks up
# the version from the `lean-toolchain` file of the project.
RUN curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
