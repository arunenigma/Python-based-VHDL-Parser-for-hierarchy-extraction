# -*- coding: utf-8 -*-
__author__ = "Arunprasath Shankar"
__copyright__ = "Copyright 2012, Arunprasath Shankar"
__license__ = "GPL"
__version__ = "1.0.1"
__email__ = "axs918@case.edu"

from project import *
from csvtohtml import *
from vhdl_facts import *

if __name__ == '__main__':
    read_lines = ''
    if not sys.argv[1].endswith('.vhd'):
        files = os.listdir(sys.argv[1])
        con = openFiles(files)
        read_lines = joinFiles(con)
    else:
        openSingleFile(sys.argv[1])
        con = openSingleFile(sys.argv[1])
        read_lines = joinFiles(con)

    out = open('itag3a.csv','wb')
    csv_write = csv.writer(out)
    csv_write.writerow(['Index','Mapped Sections','Confidence Factor','Mapped Port Name','Annotation','Module Type','Module Name','Port I/O','Port Width','Parent Module','Level','Alias Entity Location','Line'])
    vhd = VHDLtoXml(csv_write)
    vhd.parseWordsFacts()
    vhd.sectionNames()
    vhd.cleanWords()
    vhd.parseVHDL(read_lines)
    vhd.printXml()
    vhd.parseXML()
    vhd.readXML()
    vhd.xmlTree(vhd.readXML(),[0])
    wl = VHDLtoXml.tokens
    vhd.findPackageName()
    vhd.findEndPackageName()
    vhd.identifyPackageBlocks()
    vhd.packageBlocks()
    vhd.compareAB()
    vhd.tokenLines()
    vhd.finalPackageBlocks()

    print '# ---------------------------------------------  ENTITY ----------------------------------------------------'

    vhd.findEntityName()
    vhd.findEndEntityName()
    vhd.identifyEntityBlocks()
    vhd.entityBlocks()
    vhd.compareEntityAB()
    vhd.finalEntityBlocks()
    vhd.findEntityArchName()
    vhd.findEndEntityArchName()
    vhd.findEndEntityNameArch()
    vhd.archSpan()
    vhd.componentEntityLoc()
    vhd.chopTress()
    #vhd.unRollMasterDict()
    vhd.Level_1_2_3()
    out.close()

    # ----------------------------------------------------- Html Table Generation --------------------------------------

    f = csv.reader(open('itag3a.csv','rb'))
    h = open('itag3a.html','w')
    html = CsvToHTML(f,h)
    html.drawHTMLTable(f,h)

    # ----------------------------------------------------- Fact Generation --------------------------------------------

    flush = FlushOutVHDLFacts(wl)
    flush.printFacts()

    folder = './code_dump'
    for file in os.listdir(folder):
        file_path = os.path.join(folder, file)
        try:
            if os.path.isfile(file_path):
                os.unlink(file_path)
        except Exception, e:
            print e




