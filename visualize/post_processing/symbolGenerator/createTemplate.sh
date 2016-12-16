rm run.py
rm example.py
cp /tmp/testfs.py example.py
cat head.py > run.py
cat example.py >> run.py
python run.py
