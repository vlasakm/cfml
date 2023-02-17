project('fml', 'c',
  version : '0.1',
  default_options : ['warning_level=3'])

exe = executable('fml',
  'src/fml.c',
  'src/parser.c',
  'src/arena.c',
  install : true)

test('basic', exe)
