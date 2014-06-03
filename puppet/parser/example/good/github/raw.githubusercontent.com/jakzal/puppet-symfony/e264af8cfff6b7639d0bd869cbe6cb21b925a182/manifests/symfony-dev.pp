stage { 'prepare': before => Stage['main'] }

class {
    'ubuntu':  stage => prepare;
    'php-cli': stage => main;
    'php-dev': stage => main;
    'dev':     stage => main;
}
