#!/bin/sh
set -e
TMPVMT=`mktemp /tmp/XXX.vmt`
echo "creating vmt"
~/code/reve/Horn/tools/horn2vmt $1 > $TMPVMT
TMPNUXMV=`mktemp /tmp/XXX.nuxmv`
echo "creating nuxmv"
python2 ~/code/nuxmv-1.0.1-linux-x86_64/contrib/vmt2nuxmv.py $TMPVMT > $TMPNUXMV
echo "running nuxmv"
~/code/nuxmv-1.0.1-linux-x86_64/nuXmv -source ~/code/reve/Horn/tools/horn.xmv $TMPNUXMV
echo "removing tmpfiles"
rm $TMPVMT $TMPNUXMV
