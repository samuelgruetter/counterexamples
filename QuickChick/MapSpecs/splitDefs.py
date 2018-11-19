f = open('tmpSpecs2.v')
s=f.read()
cs = s.split('\n\n')
def writeFile(name, content):
    with open(name, 'w') as outf:
        outf.write(content)
for c in cs:
    name = c.replace('Definition ', '')
    i=name.index('(')
    nameC="./" + name[:i] + "_correct.v"
    print(nameC)
    nameW="./" + name[:i] + "_wrong1.v"
    print(nameW)
    writeFile(nameC, c+'\n')
    writeFile(nameW, c+'\n')
