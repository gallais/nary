#!/bin/sh
AGDA_VERSION=2.6.0.1

if ! type "agda" > /dev/null || [ ! `agda -V | sed "s/[^2]*//"` = "$AGDA_VERSION" ]; then
  cabal update
  cabal install alex happy cpphs --force-reinstalls
  cabal install Agda-"$AGDA_VERSION" --force-reinstalls
fi

mkdir -p $HOME/.agda
cp libraries $HOME/.agda/
cd $HOME/.agda/
wget https://github.com/agda/agda-stdlib/archive/v1.0.tar.gz
tar -xvzf v1.0.tar.gz
echo 'standard-library' > defaults
cd -

