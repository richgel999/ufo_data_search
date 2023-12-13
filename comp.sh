#!/bin/bash
7za a -tzip -mx=9 majestic.zip /mnt/d/dev/ufo_data_6_19/bin/majestic.json
./c.sh
cp /mnt/d/dev/ufo_data_6_19/bin/timeline*.html .
cp /mnt/d/dev/ufo_data_6_19/bin/kwic*.html .
