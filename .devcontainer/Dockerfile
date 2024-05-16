FROM ubuntu

ENV DEBIAN_FRONTEND=noninteractive \
    PATH=${PATH}:/home/idris2/.pack/bin

RUN useradd -m -s /bin/bash idris2

RUN apt-get update -y \
  && apt-get install -y \
  build-essential \
  curl \
  git \
  libgmp3-dev \
  libncurses5-dev \
  libncursesw5-dev \
  libx11-dev \
  rlwrap \
  chezscheme \
  ninja-build \
  gettext \
  cmake \
  unzip \
  tmux \
  && rm -rf /var/lib/apt/lists/

USER idris2
WORKDIR /home/idris2

RUN git clone https://github.com/stefan-hoeck/idris2-pack.git pack \
  && cd pack \
  && git checkout bb0cdc067da0d8be7922e7eb016c3fccd93059cb \
  && echo scheme | bash -c ./install.bash \
  && cd .. \
  && rm -rf pack

RUN yes yes | pack install-app idris2-lsp

USER root 
RUN git clone https://github.com/neovim/neovim.git \
  && cd neovim \
  && git checkout stable \
  && make CMAKE_BUILD_TYPE=Release \
  && make install \
  && cd .. \
  && rm -rf neovim \
  && mkdir -p /home/idris2/.local/share/nvim/site/pack/packer/start \
  && mkdir -p /home/idris2/.config/nvim \
  && git clone --depth 1 https://github.com/wbthomason/packer.nvim \
     /home/idris2/.local/share/nvim/site/pack/packer/start/packer.nvim \
  && chown -R idris2:idris2 /home/idris2/

USER idris2 

COPY --chown=idris2:idris2 ./nvim-config /home/idris2/.config/nvim

COPY --chown=idris2:idris2 ./.tmux.conf /home/idris2/.tmux.conf
ENV TERM="xterm-256color"

# RUN nvim --headless -c 'autocmd User PackerComplete quitall' -c 'PackerSync'
