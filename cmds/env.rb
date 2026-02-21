# Add repo root to load path so require 'F2_poly_mod.rb' etc. work when run from cmds/
$LOAD_PATH.unshift(File.expand_path('..', File.dirname(File.realpath(__FILE__))))
