import os
import sys

path = '/var/www/django.local'
if path not in sys.path:
    sys.path.insert(0, '/var/www/django.local')

os.environ['DJANGO_SETTINGS_MODULE'] = 'django.settings'

import django.core.handlers.wsgi
application = django.core.handlers.wsgi.WSGIHandler()
