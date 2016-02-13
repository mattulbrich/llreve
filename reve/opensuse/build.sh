rm -rf reve
cp -r ../reve .
vagrant ssh -c '/vagrant/build_static.sh'
