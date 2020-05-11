#! /bin/sh
echo $@ >> /home/vsts/work/1/s/gpg.log
export GPG_TTY=$(tty)
gpg --pinentry-mode loopback $@