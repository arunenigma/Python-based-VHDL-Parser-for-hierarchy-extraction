class CsvToHTML(object):

    def __init__(self, f, h):
        self.f = f
        self.h = h

    def drawHTMLTable(self,f,h):
        r = 0
        h.write('<!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.0 Transitional//EN" "http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd">\n')
        h.write('<html xmlns="http://www.w3.org/1999/xhtml">\n')
        h.write('<head>\n')
        h.write('<meta http-equiv="Content-Type" content="text/html; charset=utf-8" />\n')
        h.write('<title>ITAG-3A Hierarchy Table</title>\n')
        h.write('<style type="text/css">\n')
        h.write('<!--\n')
        h.write('@import url("style.css");\n')
        h.write('-->\n')
        h.write('</style>\n')
        h.write('</head>\n')
        h.write('<body>\n')
        h.write('<table id="box-table-a" summary="itag-3a vhdl hierarchy">\n')
        h.write('<thead>\n')

        for row in f:
            #print row
            if not r != 0:
                h.write('<tr>\n')
                for column in row:
                    #print column
                    h.write('<th scope="col">' + column + '</th>')

                h.write('</tr>\n')
                h.write('</thead>\n')
                h.write('<tbody>\n')
            else:
                c = 1
                for num,column in enumerate(row):
                    if c == 2:
                        e = ''
                        for i in column.split(','):
                            e = e + '<a href = \"itag3a_spec.html#section_' + i.replace('.','_').strip(" ") + '\" target = \"spec\">' + i + '</a>  '
                        h.write('<td class=\"column_' + str(c) + '\">' + e + '</td>\n')

                    elif c == 10 and not column == 'Root':
                        e = '<a href = \"itag3a_vhdl.html#' + column + '\" target = "code">'
                        h.write('<td class=\"column_' + str(c) + '\">' + e + column + '</a> </td>\n')

                    elif c == 10 and column == 'Root':
                        e = '<a href = \"itag3a_vhdl.html#' + row[num-1] + '\" target = "code">'
                        h.write('<td class=\"column_' + str(c) + '\">' + e + column + '</td>\n')

                    else:
                        h.write('<td class=\"column_' + str(c) + '\">' + column + '</td>\n')

                    c += 1

                h.write('</tr>\n')
            r += 1
        h.write('</tbody>\n')
        h.write('</table>\n')
        h.write('</body>\n')
        h.write('</html>\n')
