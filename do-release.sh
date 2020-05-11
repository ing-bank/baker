export GPG_TTY=$(tty)
sbt -Divy.home=${IVY_HOME} -Dsbt.ivy.home=${IVY_HOME} "release with-defaults"
