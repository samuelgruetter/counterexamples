f = open('tmpConjectures2.v')
s=f.read()
cs = s.split('\n\n')
def writeFile(name, content):
    with open(name, 'w') as outf:
        outf.write(content)
for c in cs:
    name = c.replace('Conjecture ', '')
    i=name.index(':')
    name="./" + name[:i] + ".v"
    print(name)
    writeFile(name, c+'\n')
