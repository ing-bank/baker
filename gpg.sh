#! /bin/sh
export GPG_TTY=$(tty)
/usr/bin/gpg --pinentry-mode loopback $@
