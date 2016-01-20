#!/usr/bin/env bash
cat <<'EOF' > /etc/pacman.d/mirrorlist
Server = https://k42.ch/mirror/archlinux/$repo/os/$arch
Server = http://mirror.netcologne.de/archlinux/$repo/os/$arch
Server = http://ftp.fau.de/archlinux/$repo/os/$arch
Server = https://mirror.f4st.host/archlinux/$repo/os/$arch
Server = https://arch.jensgutermuth.de/$repo/os/$arch
Server = https://mirror.pseudoform.org/$repo/os/$arch
Server = http://ftp.halifax.rwth-aachen.de/archlinux/$repo/os/$arch
Server = http://ftp.hosteurope.de/mirror/ftp.archlinux.org/$repo/os/$arch
Server = https://mirror.fluxent.de/archlinux/$repo/os/$arch
Server = http://mirrors.niyawe.de/archlinux/$repo/os/$arch
Server = https://archlinux.honkgong.info/$repo/os/$arch
Server = http://ftp.hawo.stw.uni-erlangen.de/archlinux/$repo/os/$arch
Server = http://mirror.23media.de/archlinux/$repo/os/$arch
Server = http://mirror5.bastelfreak.org/archlinux/$repo/os/$arch
Server = https://mirror.js-webcoding.de/pub/archlinux/$repo/os/$arch
EOF
pacman -Syu --noconfirm
pacman -S llvm --noconfirm
pacman -S clang --noconfirm
pacman -S cmake --noconfirm
