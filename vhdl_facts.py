__author__ = 'arunprasathshankar'
class FlushOutVHDLFacts(object):

    def __init__(self,wl):
        self.wl = wl

    def printFacts(self):
        facts_out = open('vhdl_facts.txt','wb')
        facts_out.write('(deffacts VHDLfacts\n')
        for word in self.wl:
            word[0] = word[0].split(' ')
            word[1] = word[1].replace('"',' ')
            facts_out.write( '(word-data(word-name "' + word[1] + '")(line-number ' + word[0][3] + ')(word-number ' + word[0][5] + '))\n' )
        facts_out.write(')')
        facts_out.close()
