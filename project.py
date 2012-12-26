# -*- coding: utf-8 -*-
__author__ = "Arunprasath Shankar"
__copyright__ = "Copyright 2012, Arunprasath Shankar"
__license__ = "GPL"
__version__ = "1.0.1"
__email__ = "axs918@case.edu"

from difflib import SequenceMatcher
from collections import defaultdict
import lxml.etree as et
import numpy as np
import operator
import shutil
import math
import time
import csv
import sys
import os
import re

def openFiles(files):
    dest = './code_dump'
    for file in files:
        f = os.path.join(sys.argv[1], file)
        if os.path.isfile(f):
            if '.vhd' in f:
                shutil.copy(f,dest)

    d = os.listdir(dest)
    new_file = ''
    for file in d:
        if '.vhd' in file:
            new_file = file.replace('.vhd', '.txt')
            os.rename(os.path.join(dest, file), os.path.join(dest, new_file))

    new_files = os.listdir(dest)
    content = ''
    for f in new_files:
        if '.txt' in f:
            content = content + '\n' + open(dest + '/' + f,'rb').read()
    return content

def joinFiles(c):
    joined_w = open('joined_file.txt','wb').write(c)
    joined_r = open('joined_file.txt','rb')
    lines = joined_r.readlines()
    return lines

def openSingleFile(file_path):
    dest = './code_dump'
    shutil.copy(file_path,dest)
    d = os.listdir(dest)
    new_file = ''
    for file in d:
        if '.vhd' in file:
            new_file = file.replace('.vhd', '.txt')
            os.rename(os.path.join(dest, file), os.path.join(dest, new_file))

    new_files = os.listdir(dest)
    content = ''
    for f in new_files:
        if '.txt' in f:
            content = content + '\n' + open(dest + '/' + f,'rb').read()
    return content


root = et.Element('root')
tree = et.ElementTree(root)

file = open('all_words_facts.txt','rb')

class VHDLtoXml(object):
    counter = 1
    tokens, new_tokens = [], []
    packages, entities, components = [], [], []
    ports, records, processes, generates, functions = [], [], [], [], []
    types, architectures, ends = [], [], []
    constants = {}

    blocks, ent_blocks = [], []
    a, b, c = [], [], []
    found_package_names = []
    found_package_body_names = []
    found_end_package_names = []
    complicated_package_ends = []
    comp_start = []

    found_entity_names = []
    found_entity_body_names = []
    found_end_entity_names = []
    complicated_entity_ends = []

    found_entity_arch_names = []
    found_end_entity_arch_names = []

    ent_name, end_arch, comp_span, port_span = [], [], [], []
    clash, temp = [], []

    all_words, secs = [], []
    entity_ports, entity_generates, entity_processes,  entity_functions = {}, {}, {}, {}
    super_ent, width = '', ''
    master, cel = {}, {}
    all_components, generic_list, c_span = [], [], []
    clean_words = defaultdict(list)

    def __init__(self,csv_write):
        self.csv_write = csv_write

    def parseWordsFacts(self):
        fact = file.readline()
        while not fact == "":
            fact.replace( "\n", "" )
            fact = file.readline()
            fact = fact.replace('(',' ')
            fact = fact.replace(')',' ')
            fact = fact.replace('word-data word "','|')
            fact = fact.replace('"  spec-id 1  location-id ','|')
            fact = fact.replace('  ','|')
            words = fact.split('|')
            self.all_words.append(words)

    def sectionNames(self):
        for word in self.all_words:
            if len(word) > 1:
                if re.findall(r"(\d*(?:\.\d+))",word[1]):
                    if not re.findall(r"([a-zA-Z])",word[1]) and not word[1].startswith('0'):
                        if not word[1].endswith(':') and not 'Link' in word[3]:
                            self.secs.append([word[1].translate(None, ":;,"),word[2],word[3]])

    def cleanWords(self):
        self.all_words.remove(self.all_words[-1])
        for word in self.all_words:
            word.remove(word[0])
            word.remove(word[3])
            word[0] = word[0].translate(None,"\t\r")
            word[0] = word[0].replace(',','')
            word[0] = word[0].replace(' ','')
            if len(word[0]) > 2 and '_' in word[0] or 'TD' in word[2]:
                self.clean_words[word[0].lower()].append(word[1])
                word.remove(word[2])

    def valid_XML_char_ordinal(self, i):
        return 32 <= i <= 55295 or i in (9, 10, 13) or 57344 <= i <= 65533 or 65536 <= i <= 1114111

    def parseVHDL(self,read_lines):
        for line in read_lines:
            elements = line.split(' ')
            elements = filter(None, elements)
            line = et.SubElement(root, 'line')
            length = len(elements)
            for i in range(length):
                elements[i] = ''.join((c for c in elements[i] if VHDLtoXml.valid_XML_char_ordinal(self, ord(c))))
                elements[i] = elements[i].decode('utf8')
                elements[i] = elements[i].rstrip('\n')
                item = et.SubElement(line, 'item')
                item.text = elements[i]

    def printXml(self):
        tree.write('out.xml', pretty_print = True, xml_declaration = True, encoding = 'utf-8')

    def parseXML(self):
        path = './out.xml'
        parser = et.XMLParser(recover = True)
        f = et.parse(path, parser)
        fstring = et.tostring(f, pretty_print = True)
        fstring = fstring.replace('<line/>', '')
        return fstring

    def readXML(self):
        element = et.fromstring(VHDLtoXml.parseXML(self))
        return element

    def xmlTree(self, branch, index):
        if branch.text is not None:
            branch.text = branch.text.encode('ascii', 'ignore')
            #print branch.text  <== use it to generate line facts
            if not branch.getchildren():
                word = branch.text
                self.word_location = ['{0}'.format(index), word]
                self.tokens.append(self.word_location)
                self.word_location[0] = self.word_location[0].replace('[', ' ')
                self.word_location[0] = self.word_location[0].replace(']', ' ')
                self.nums = self.word_location[0].split(' ')

                for n in self.nums:
                    if n == '':
                        self.nums.remove(n)
                VHDLtoXml.filterPackages(self)
                VHDLtoXml.filterFunctions(self)
                VHDLtoXml.filterEntities(self)
                VHDLtoXml.filterComponents(self)
                VHDLtoXml.filterPorts(self)
                VHDLtoXml.filterRecords(self)
                VHDLtoXml.filterProcesses(self)
                VHDLtoXml.filterGenerates(self)
                VHDLtoXml.filterEnds(self)
                VHDLtoXml.filterTypes(self)
                VHDLtoXml.filterArchitectures(self)

            else:
                for subtree in range(0, len(branch)):
                    VHDLtoXml.xmlTree(self, branch[subtree], '{0}[{1}]'.format(index, subtree))

    def filterPackages(self):
        if self.word_location[1] == 'package' and self.nums[2] == '0':
            self.packages.append(self.word_location)

    def findPackageName(self):
        for i, package in enumerate(self.packages):
            for j, token in enumerate(self.tokens):
                if package == token and not self.tokens[j + 1][1] == 'body' and not self.tokens[j + 1][1] == 'body;':
                    self.tokens[j + 1][1] = self.tokens[j + 1][1].replace(';', '')
                    self.tokens[j + 1][1] = self.tokens[j + 1][1].translate(None, "\t\r\n")
                    self.found_package_names.append([self.tokens[j][1], self.tokens[j + 1][1], self.tokens[j][0]])
                if package == token and self.tokens[j + 1][1] == 'body':
                    self.tokens[j + 1][1] = self.tokens[j + 1][1].replace(';', '')
                    self.tokens[j + 1][1] = self.tokens[j + 1][1].translate(None, "\t\r\n")
                    self.tokens[j][1] += ' body'
                    self.found_package_names.append([self.tokens[j][1], self.tokens[j + 2][1], self.tokens[j][0]])
                if package == token and self.tokens[j + 1][1] == 'body;':
                    pass

    def filterFunctions(self):
        if self.word_location[1] == 'function' and self.nums[2] == '0':
            self.functions.append(self.word_location)

    def filterEntities(self):
        if self.word_location[1] == 'entity' and self.nums[2] == '0':
            self.entities.append(self.word_location)

    def filterComponents(self):
        if self.word_location[1] == 'component' and self.nums[2] == '0':
            self.components.append(self.word_location)

    def filterPorts(self):
        if self.word_location[1] == 'port' and self.nums[2] == '0':
            self.ports.append(self.word_location)

    def filterRecords(self):
        if self.word_location[1] == 'record' and self.nums[2] == '0':
            self.records.append(self.word_location)

    def filterProcesses(self):
        if self.word_location[1] == 'process' and self.nums[2] == '0':
            self.processes.append(self.word_location)

    def filterGenerates(self):
        if self.word_location[1] == 'generate' and self.nums[2] == '0':
            self.generates.append(self.word_location)

    def filterEnds(self):
        if self.word_location[1] == 'end' or self.word_location[1] == 'end;':
            self.ends.append(self.word_location)

    def filterTypes(self):
        if self.word_location[1] == 'type' and self.nums[2] == '0':
            self.types.append(self.word_location)

    def filterArchitectures(self):
        if self.word_location[1] == 'architecture' and self.nums[2] == '0':
            self.architectures.append(self.word_location)

    def findEndPackageName(self):
        for i, end in enumerate(self.ends):
            for j, token in enumerate(self.tokens):
                if end == token and not end[1] == 'end;':
                    if not self.tokens[j + 1][1] == 'package':
                        if (j+1) < len(self.tokens):
                            self.tokens[j + 1][1] = self.tokens[j + 1][1].replace(';library', '')
                            self.tokens[j + 1][1] = self.tokens[j + 1][1].translate(None, ";\t\r\n")
                            self.found_end_package_names.append([end[1], self.tokens[j + 1][1], end[0]])

                    if self.tokens[j + 1][1] == 'package' and not self.tokens[j + 2][1] == 'body':
                        if (j+2) < len(self.tokens):
                            self.tokens[j + 2][1] = self.tokens[j + 2][1].replace(';library', '')
                            self.tokens[j + 2][1] = self.tokens[j + 2][1].translate(None, ";\t\r\n")
                            tag = end[1] + ' package'
                            self.found_end_package_names.append([tag, self.tokens[j + 2][1], end[0]])

                    if self.tokens[j + 1][1] == 'package' and self.tokens[j + 2][1] == 'body':
                        if (j+3) < len(self.tokens):
                            self.tokens[j + 3][1] = self.tokens[j + 3][1].replace(';library', '')
                            self.tokens[j + 3][1] = self.tokens[j + 3][1].translate(None, ";\t\r\n")
                            tag = end[1] + ' package body'
                            self.found_end_package_names.append([tag, self.tokens[j + 3][1], end[0]])

                    if end == token and not end[1] == 'end;':
                        if j + 3 < len(self.tokens):
                            if self.tokens[j + 1][1] == 'package' and self.tokens[j + 2][1] == 'body' and self.tokens[j + 3][1] in ('library', ''):
                                special = 'end package body;'
                                self.complicated_package_ends.append([special, end[0]])

    def identifyPackageBlocks(self):
        for i, package in enumerate(self.found_package_names):
            for j, end in enumerate(self.found_end_package_names):
                if package[1] == end[1]:
                    self.blocks.append([package, end])

    def packageBlocks(self):
        for i, block in enumerate(self.blocks):
            if i + 1 < len(self.blocks):
                if self.blocks[i][0][0] == self.blocks[i + 1][0][0] and self.blocks[i][0][1] == self.blocks[i + 1][0][1] and self.blocks[i][0][2] == self.blocks[i + 1][0][2]:
                    if self.blocks[i][0][0] == 'package':
                        self.blocks.remove(self.blocks[i + 1])
                    if self.blocks[i][0][0] == 'package body':
                        self.blocks.remove(self.blocks[i])
                if self.blocks[i][0][0] == 'package' and self.blocks[i + 1][0][0] == 'package body' and self.blocks[i][0][1] == self.blocks[i + 1][0][1] and self.blocks[i][1][1] == self.blocks[i + 1][1][1]:
                    if not self.blocks[i][0][2] == self.blocks[i + 1][0][2] and self.blocks[i][1][2] == self.blocks[i + 1][1][2]:
                        self.a.append(self.blocks[i + 1])
                        self.blocks.remove(self.blocks[i + 1])

        for block in self.blocks:
            self.b.append(block)

    def compareAB(self):
        for a in self.a:
            for b in self.b:
                if a[0] == b[0]:
                    self.a.remove(a)

            for a in self.a:
                for b in self.b:
                    if a[0][0] == b[0][0] and a[0][1] == b[0][1]:
                        self.a.remove(a)
            self.c = self.a

    def tokenLines(self):
        for token in self.tokens:
            loc = token[0].split(' ')
            loc = loc[3]
            tok = token[1]
            token = [loc,tok]
            self.new_tokens.append(token)

    def finalPackageBlocks(self):

        # collecting CONSTANTS
        for i,token in enumerate(self.new_tokens):
            if token[1] == 'CONSTANT' or token[1] == 'constant':
                if not 'std_logic_vector' in self.new_tokens[i+3][1] and not 'STD_LOGIC_VECTOR' in self.new_tokens[i+3][1]:
                    if len(self.new_tokens[i+5][1]) < 5:
                        if (i+5) < len(self.new_tokens):
                            if re.findall(r'\d+',self.new_tokens[i+5][1]):
                                r = re.findall(r'\d+',self.new_tokens[i+5][1])
                                self.constants[(self.new_tokens[i+1][1]).translate(None,'\t:')] = r[0]

            if 'CONSTANT' in token[1].translate(None,'\t') or 'constant' in token[1].translate(None,'\t'):
                if 'integer:=' in self.new_tokens[i+1][1]:
                    c = self.new_tokens[i+1][1].split('\t')[0]
                    con = c.split(':')[0]
                    d = re.findall(r'\d+',self.new_tokens[i+1][1])
                    self.constants[con.translate(None,'\t:')] = d[0]

                if not self.new_tokens[i+2][1] == ':=' and ':=' in self.new_tokens[i+2][1]:
                    if re.findall(r'\d+',self.new_tokens[i+2][1]):
                        r = re.findall(r'\d+',self.new_tokens[i+2][1])
                        self.constants[(self.new_tokens[i+1][1]).translate(None,'\t:')] = r[0]

                if not self.new_tokens[i+3][1] == ':=' and ':=' in self.new_tokens[i+3][1]:
                    if re.findall(r'\d+',self.new_tokens[i+3][1]):
                        r = re.findall(r'\d+',self.new_tokens[i+3][1])
                        c = self.new_tokens[i+1][1].translate(None,'\t')
                        con = c.split(':')[0]
                        self.constants[con.translate(None,'\t:')] = r[0]

        for i, c in enumerate(self.c):
            self.c[i][1] = self.complicated_package_ends[i]

        for c in self.c:
            self.blocks.append(c)

        # Filtering package body
        for block in self.blocks:
            if block[0][0] == 'package body':
                self.blocks.remove(block)

        for block in self.blocks:
            pin_s = 0
            pin_e = 0
            sec_split = []
            if not len(block[1]) == 2:
                p1 = [block[0][1:]][0]
                p2 = [block[1][1:]][0]
                p1 = p1[::-1]
                p2 = p2[::-1]
                p1 = p1[0].split(' ')
                p2 = p2[0].split(' ')
                p1 = p1[3]
                p2 = p2[3]

                for i,token in enumerate(self.new_tokens):
                    if p1 == token[0]:
                        pin_s = i

                for i,token in enumerate(self.new_tokens):
                    if p2 == token[0]:
                        pin_e = i

                span = self.new_tokens[pin_s:pin_e]
                #print block[0][0],block[0][1]  # Printing Package(Root)
                hints_fn = block[0][1]
                sec_ports = VHDLtoXml.vhdlSpecMapper(self,hints_fn)
                for section in sec_ports[0]:
                    sec_split.append(section.split(' '))

                sec = {}

                for i,sc in enumerate(sec_split):
                    sec[sc[0]] = sc[1]

                sorted_sec = sorted(sec.iteritems(), key = operator.itemgetter(1),reverse = True)

                if not len(sorted_sec) < 1 and not sorted_sec is None:
                    self.ss = sorted_sec[0][0]

                else:
                    self.ss = ''

                self.csv_write.writerow([self.counter,self.ss,str(sorted_sec).translate(None,"[]\""),'-','',block[0][0],block[0][1],'-','-','Root','1','-',str(p1)])
                self.counter += 1
                del sec_split[:]

                for i,s in enumerate(span):
                    s[1] = s[1].replace('\t','')
                    sec_split = []
                    if s[1] == 'function':
                        func_name = span[i+1][1]
                        func_name = func_name.replace('(',' ')
                        func_name = func_name.split(' ')
                        func_name = func_name[0]
                        #print '|_______  ' + s[1],func_name
                        hints_fn = func_name
                        sec_ports = VHDLtoXml.vhdlSpecMapper(self,hints_fn)
                        for section in sec_ports[0]:
                            sec_split.append(section.split(' '))

                        sec = {}

                        for i,sc in enumerate(sec_split):
                            sec[sc[0]] = sc[1]

                        sorted_sec = sorted(sec.iteritems(), key = operator.itemgetter(1),reverse = True)

                        if not len(sorted_sec) < 1 and not sorted_sec is None:
                            self.ss = sorted_sec[0][0]

                        else:
                            self.ss = ''
                        self.csv_write.writerow([self.counter,self.ss,str(sorted_sec).translate(None,"[]\""),'-','',s[1],func_name,'-','-',block[0][1],'2','-',s[0]])
                        self.counter += 1
                        del sec_split[:]

                    # record
                    sec_split = []
                    if s[1] == 'type':
                        rec_name = span[i+1][1]
                        rec_name = rec_name.replace('(',' ')
                        rec_name = rec_name.split(' ')
                        rec_name = rec_name[0]
                        if not rec_name == ':':
                            #print '|_______  ' + 'record',rec_name

                            hints_fn = rec_name
                            sec_ports = VHDLtoXml.vhdlSpecMapper(self,hints_fn)
                            for section in sec_ports[0]:
                                sec_split.append(section.split(' '))

                            sec = {}

                            for i,sc in enumerate(sec_split):
                                sec[sc[0]] = sc[1]

                            sorted_sec = sorted(sec.iteritems(), key = operator.itemgetter(1),reverse = True)

                            if not len(sorted_sec) < 1 and not sorted_sec is None:
                                self.ss = sorted_sec[0][0]

                            else:
                                self.ss = ''
                            self.csv_write.writerow([self.counter,self.ss,str(sorted_sec).translate(None,"[]\""),'-','','record',rec_name,'-','-',block[0][1],'2','-',s[0]])
                            self.counter += 1
                            del sec_split[:]

                    sec_split = []
                    if s[1] == 'component':
                        self.comp_start.append(s[0])

                        comp_name = span[i+1][1]
                        comp_name = comp_name.replace('(',' ')
                        comp_name = comp_name.split(' ')
                        comp_name = comp_name[0]
                        self.comp_name = "".join(comp_name.split())
                        if not self.comp_name == 'end':
                            if not self.comp_name == 'component':
                                #print '|____________' + s[1],self.comp_name

                                hints_fn = self.comp_name
                                #if VHDLtoXml.vhdlSpecMapper(self,hints_fn):
                                sec_ports = VHDLtoXml.vhdlSpecMapper(self,hints_fn)
                                for section in sec_ports[0]:
                                    sec_split.append(section.split(' '))

                                sec = {}

                                for i,sc in enumerate(sec_split):
                                    sec[sc[0]] = sc[1]

                                sorted_sec = sorted(sec.iteritems(), key = operator.itemgetter(1),reverse = True)

                                if not len(sorted_sec) < 1 and not sorted_sec is None:
                                    self.ss = sorted_sec[0][0]

                                else:
                                    self.ss = ''
                                self.csv_write.writerow([self.counter,self.ss,str(sorted_sec).translate(None,"[]\""),'-','',s[1],self.comp_name,'-','-',block[0][1],'2','-',s[0]])
                                self.counter += 1
                                del sec_split[:]

                    if (i+1) < len(span):
                        if span[i-1][1] == 'end' and span[i][1] == 'component;':
                            self.comp_span.append(s[0])
                            VHDLtoXml.printPortsParallel(self,self.constants)

                    if (i+1) < len(span):
                        if span[i][1] == 'end' and span[i+1][1] == 'component':
                            self.comp_span.append(s[0])
                            VHDLtoXml.printPortsParallel(self,self.constants)


                    sec_split = []
                    if s[1] == 'process':
                        process_name = span[i+1][1]
                        process_name = process_name.replace('(',' ')
                        process_name = process_name.split(' ')
                        process_name = process_name[0]
                        #print '|_______  ' + s[1],process_name

                        hints_fn = process_name
                        sec_ports = VHDLtoXml.vhdlSpecMapper(self,hints_fn)
                        for section in sec_ports[0]:
                            sec_split.append(section.split(' '))

                        sec = {}

                        for i,sc in enumerate(sec_split):
                            sec[sc[0]] = sc[1]

                        sorted_sec = sorted(sec.iteritems(), key = operator.itemgetter(1),reverse = True)

                        if not len(sorted_sec) < 1 and not sorted_sec is None:
                            self.ss = sorted_sec[0][0]

                        else:
                            self.ss = ''
                        self.csv_write.writerow([self.counter,self.ss,str(sorted_sec).translate(None,"[]\""),'','',s[1],process_name,'-','-',block[0][1],'2','-','-',s[0]])
                        self.counter += 1
                        del sec_split[:]

                    sec_split = []
                    if s[1] == 'generate':
                        generate_name = span[i+1][1]
                        generate_name = generate_name.replace('(',' ')
                        generate_name = generate_name.split(' ')
                        generate_name = generate_name[0]
                        #print '|_______  ' + s[1],generate_name
                        hints_fn = generate_name
                        sec_ports = VHDLtoXml.vhdlSpecMapper(self,hints_fn)
                        print sec_ports[0], sec_ports[1]

                        for section in sec_ports[0]:
                            sec_split.append(section.split(' '))

                        sec = {}

                        for i,sc in enumerate(sec_split):
                            sec[sc[0]] = sc[1]

                        sorted_sec = sorted(sec.iteritems(), key = operator.itemgetter(1),reverse = True)

                        if not len(sorted_sec) < 1 and not sorted_sec is None:
                            self.ss = sorted_sec[0][0]

                        else:
                            self.ss = ''
                        self.csv_write.writerow([self.counter,self.ss,str(sorted_sec).translate(None,"[]\""),'','',s[1],generate_name,'-','-',block[0][1],'2','-',s[0]])
                        self.counter += 1
                        del sec_split[:]

            else:
                if not block[0][0] == 'package body':
                    p1 = [block[0][1:]][0]
                    p2 = [block[1][1:]][0]
                    p1 = p1[::-1]
                    p2 = p2[::-1]
                    p1 = p1[0].split(' ')
                    p2 = p2[0].split(' ')
                    p1 = p1[3]
                    p2 = p2[3]

                    for i,token in enumerate(self.new_tokens):
                        if p1 == token[0]:
                            pin_s = i

                    for i,token in enumerate(self.new_tokens):
                        if p2 == token[0]:
                            pin_e = i

                    span = self.new_tokens[pin_s:pin_e]
                    #print block[0][0],block[0][1]

                    for i,s in enumerate(span):
                        if s[1] == 'function':
                            func_name = span[i+1][1]
                            func_name = func_name.replace('(',' ')
                            func_name = func_name.split(' ')
                            func_name = func_name[0]
                            #print '|_______  ' + s[1],func_name

                        if s[1] == 'type':
                            rec_name = span[i+2][1]
                            rec_name = rec_name.replace('(',' ')
                            rec_name = rec_name.split(' ')
                            rec_name = rec_name[0]
                            #print '|_______  ' + 'record',rec_name

                        if s[1] == 'component':
                            comp_name = span[i+1][1]
                            comp_name = comp_name.replace('(',' ')
                            comp_name = comp_name.split(' ')
                            comp_name = comp_name[0]
                            comp_name = "".join(comp_name.split())
                            if not comp_name == 'component':
                                pass
                                #print '|_______  ' + s[1],comp_name

                        if s[1] == ':':
                            port_name = span[i-1][1]
                            port_name = port_name.replace('(',' ')
                            port_name = port_name.split(' ')
                            port_name = port_name[0]
                            port_name = "".join(port_name.split())
                            #print '|_______  ' + 'port',port_name

                        if s[1] == 'process':
                            process_name = span[i+1][1]
                            process_name = process_name.replace('(',' ')
                            process_name = process_name.split(' ')
                            process_name = process_name[0]
                            #print '|_______  ' + s[1],process_name

                        if s[1] == 'generate':
                            generate_name = span[i+1][1]
                            generate_name = generate_name.replace('(',' ')
                            generate_name = generate_name.split(' ')
                            generate_name = generate_name[0]
                            #print '|_______  ' + s[1],generate_name

            # ----------------------------------------------------- Printing Ports ----------------------------------------------------

    def unique_items(self,L):
        found = set()
        for item in L:
            if item[0] not in found:
                yield item
                found.add(item[0])

    def portIOAndWidth(self,x,y,g_list,con):
        ele_list = []
        gen_var = []
        gen_val = []
        width_map = {}
        self.width = ''

        if x == 'std_logic' or x == 'STD_LOGIC' or x == 'std_logic;' or x == 'std_logic);':
            self.width = '1'

        if x == 'std_logic_vector' or x == 'STD_LOGIC_VECTOR' :
            y = y.replace('(','')
            if y.isdigit():
                self.width = str(self.width)
            else:
                y = y.split('-')
                self.ele = y[0]

                if len(g_list) > 0:
                    for j,tok in enumerate(g_list[0]):
                        if tok == 'generic':
                            g = g_list[0][j+1].translate(None,',.;:()')
                            if not g == '':
                                gen_var.append(g)
                        if ':' in tok and not tok == ':' and not tok == ':=' and not '=' in tok:
                            t = tok.split(':')
                            if not t[0] == '':
                                gen_var.append(t[0].translate(None,':,().;'))
                        if tok == ':':
                            if not g_list[0][j-1] == '':
                                gen_var.append(g_list[0][j-1].translate(None,':,().;'))

                    for j,tok in enumerate(g_list[0]):
                        if ':=' in tok and not tok == ':=':
                            if re.findall(r'\d+',tok):
                                r = re.findall(r'\d+',tok)
                                if not r[0] == '' and not 'port' in r[0]:
                                    gen_val.append(r[0].translate(None,':,().;'))

                            if re.findall(r'\d+',g_list[0][j+1]):
                                r = re.findall(r'\d+',g_list[0][j+1])
                                if not r[0] == '' and not 'port' in r[0]:
                                    gen_val.append(r[0].translate(None,':,().;'))
                            else:
                                if not g_list[0][j+1] == '' and not 'port' in g_list[0][j+1]:
                                    gen_val.append(g_list[0][j+1].translate(None,':,().;'))

                        if tok == ':=':
                            if re.findall(r'\d+',g_list[0][j+1]):
                                r = re.findall(r'\d+',g_list[0][j+1])
                                if not r[0] == '' and not 'port' in r[0]:
                                    gen_val.append(r[0].translate(None,':,().;'))
                            else:
                                if not g_list[0][j+1] == '' and not 'port' in g_list[0][j+1]:
                                    gen_val.append(g_list[0][j+1].translate(None,':,().;'))

                width_map = dict(zip(gen_var, gen_val))
                #print width_map
                for key,value in width_map.iteritems():
                    if self.ele.lower() == key.lower():
                        if str(value).isdigit():
                            self.width = str(value)
                        else:
                            for key,value in con.items():
                                if value.lower() == key.lower():
                                    self.width = str(value)

                    else:
                        for key,value in con.items():
                            if self.ele.lower() == key.lower():
                                if str(value).isdigit():
                                    self.width = str(value)
                                else:
                                    for key,value in con.items():
                                        if value.lower() == key.lower():
                                            self.width = str(value)

                if width_map == {}:
                    for key,value in con.items():
                        if self.ele.lower() == key.lower():
                            self.width = str(value)


        if 'STD_LOGIC_VECTOR(' in x or 'std_logic_vector(' in x:
            x = x.replace('STD_LOGIC_VECTOR(','')
            x = x.replace('std_logic_vector(','')
            x = x.split('-')[0]
            self.ele = x
            if len(g_list) > 0:
                for j,tok in enumerate(g_list[0]):
                    if tok == 'generic':
                        g = g_list[0][j+1].translate(None,',.;:()')
                        if not g == '':
                            gen_var.append(g)
                    if ':' in tok and not tok == ':' and not tok == ':=' and not '=' in tok:
                        t = tok.split(':')
                        if not t[0] == '':
                            gen_var.append(t[0].translate(None,':,().;'))
                    if tok == ':':
                        if not g_list[0][j-1] == '':
                            gen_var.append(g_list[0][j-1].translate(None,':,().;'))

                for j,tok in enumerate(g_list[0]):
                    if ':=' in tok and not tok == ':=':
                        if re.findall(r'\d+',tok):
                            r = re.findall(r'\d+',tok)
                            if not r[0] == '' and not 'port' in r[0]:
                                gen_val.append(r[0].translate(None,':,().;'))

                        if re.findall(r'\d+',g_list[0][j+1]):
                            r = re.findall(r'\d+',g_list[0][j+1])
                            if not r[0] == '' and not 'port' in r[0]:
                                gen_val.append(r[0].translate(None,':,().;'))
                        else:
                            if not g_list[0][j+1] == '' and not 'port' in g_list[0][j+1]:
                                gen_val.append(g_list[0][j+1].translate(None,':,().;'))

                    if tok == ':=':
                        if re.findall(r'\d+',g_list[0][j+1]):
                            r = re.findall(r'\d+',g_list[0][j+1])
                            if not r[0] == '' and not 'port' in r[0]:
                                gen_val.append(r[0].translate(None,':,().;'))
                        else:
                            if not g_list[0][j+1] == '' and not 'port' in g_list[0][j+1]:
                                gen_val.append(g_list[0][j+1].translate(None,':,().;'))

            width_map = dict(zip(gen_var, gen_val))
            #print width_map
            for key,value in width_map.iteritems():
                if self.ele.lower() == key.lower():
                    if str(value).isdigit():
                        self.width = str(value)
                    else:
                        for key,value in con.items():
                            if value.lower() == key.lower():
                                self.width = str(value)

                else:
                    for key,value in con.items():
                        if self.ele.lower() == key.lower():
                            if str(value).isdigit():
                                self.width = str(value)
                            else:
                                for key,value in con.items():
                                    if value.lower() == key.lower():
                                        self.width = str(value)
            if width_map == {}:
                for key,value in con.items():
                    if self.ele.lower() == key.lower():
                        self.width = str(value)
        return 1

    def printPortsParallel(self,con):
        cs = []
        self.found_port = []
        cs = self.comp_span[-2:]

        if len(cs) == 1:
            cs.append(self.comp_start[0])
            cs.sort()

        if not cs is None and len(cs) == 2:
            piv_1 = int(cs[0])
            piv_2 = int(cs[1])
            self.port_span = []
            for i,tok in enumerate(self.new_tokens):
                if int(tok[0]) > piv_1 and not int(tok[0]) >= piv_2:
                    self.port_span.append(tok[1])

        # computing port span
        if not self.port_span == [] and not self.port_span == ['']:
            for ps in self.port_span:
                if ps == '' or ps == ' ':
                    self.port_span.remove(ps)

        # ------------------------------------------------------------------------------------------------------------
        port_list = []
        self.generic_list = []

        for i,ps in enumerate(self.port_span):
            if ps == 'generic' or ps == 'generic(':
                self.generic_list.append(self.port_span[i:i+50])


        for i,ps in enumerate(self.port_span):
            if ps == ':' and self.port_span[i+1] == 'in' and not self.port_span[i-2] == 'signal' and not self.port_span[i-3] == 'function':
                if (i+3) < len(self.port_span):
                    if VHDLtoXml.portIOAndWidth(self,self.port_span[i+2],self.port_span[i+3],self.generic_list,con):
                        port_list.append([self.port_span[i-1],self.port_span[i+1],self.width])

            if ps == ':' and self.port_span[i+1] == 'out'and not self.port_span[i-2] == 'signal' and not self.port_span[i-3] == 'function':
                if (i+3) < len(self.port_span):
                    if VHDLtoXml.portIOAndWidth(self,self.port_span[i+2],self.port_span[i+3],self.generic_list,con):
                        port_list.append([self.port_span[i-1],self.port_span[i+1],self.width])

            if ps == ':' and self.port_span[i+1] == 'IN'and not self.port_span[i-2] == 'signal' and not self.port_span[i-3] == 'function':
                if (i+3) < len(self.port_span):
                    if VHDLtoXml.portIOAndWidth(self,self.port_span[i+2],self.port_span[i+3],self.generic_list,con):
                        port_list.append([self.port_span[i-1],self.port_span[i+1],self.width])

            if ps == ':' and self.port_span[i+1] == 'OUT'and not self.port_span[i-2] == 'signal' and not self.port_span[i-3] == 'function':
                if (i+3) < len(self.port_span):
                    if VHDLtoXml.portIOAndWidth(self,self.port_span[i+2],self.port_span[i+3],self.generic_list,con):
                        port_list.append([self.port_span[i-1],self.port_span[i+1],self.width])

            if ps.endswith(':') and len(ps) > 1 and self.port_span[i+1] == 'in':
                if (i+3) < len(self.port_span):
                    if VHDLtoXml.portIOAndWidth(self,self.port_span[i+2],self.port_span[i+3],self.generic_list,con):
                        port_list.append([self.port_span[i],self.port_span[i+1],self.width])

            if ps.endswith(':') and len(ps) > 1 and self.port_span[i+1] == 'out':
                if (i+3) < len(self.port_span):
                    if VHDLtoXml.portIOAndWidth(self,self.port_span[i+2],self.port_span[i+3],self.generic_list,con):
                        port_list.append([self.port_span[i],self.port_span[i+1],self.width])

            if ps.endswith(':') and len(ps) > 1 and self.port_span[i+1] == 'IN':
                if (i+3) < len(self.port_span):
                    if VHDLtoXml.portIOAndWidth(self,self.port_span[i+2],self.port_span[i+3],self.generic_list,con):
                        port_list.append([self.port_span[i],self.port_span[i+1],self.width])

            if ps.endswith(':') and len(ps) > 1 and self.port_span[i+1] == 'OUT':
                if (i+3) < len(self.port_span):
                    if VHDLtoXml.portIOAndWidth(self,self.port_span[i+2],self.port_span[i+3],self.generic_list,con):
                        port_list.append([self.port_span[i],self.port_span[i+1],self.width])

        # ------------------------------------------------------------------------------------------------------------

        # remove duplicates

        port_list =  list(VHDLtoXml.unique_items(self,port_list))

        if not port_list == self.temp and not port_list == []:
            self.temp = port_list
            sec_split = []
            found_port = []
            for no,port in enumerate(port_list):
                port[0]  = port[0].translate(None,':();')
                #print '|_____________________ port ' + port[0] + '  ' + port[1] + '  ' + port[2]

                hints_fn = port[0]
                hints = hints_fn.split('_')
                sec_ports = VHDLtoXml.vhdlSpecMapper(self,hints_fn)
                for section in sec_ports[0]:
                    sec_split.append(section.split(' '))

                sec = {}
                for i,sc in enumerate(sec_split):
                    sec[sc[0]] = sc[1]
                sorted_sec = sorted(sec.iteritems(), key = operator.itemgetter(1),reverse = True)

                if not len(sorted_sec) < 1 and not sorted_sec is None:
                    self.ss = sorted_sec[0][0]
                else:
                    self.ss = ''

                sec_ports[1] = str(list(set(sec_ports[1])))

                # splitting self.temp -> entity name
                first_ent = str(self.comp_name).split('_')

                for p in sec_ports[1]:
                    if hints_fn == port:
                        found_port.append(port)

                for p in sec_ports[1]:
                    if first_ent[0] in p:
                        if hints[-1].lower() in p:
                            found_port.append(p)

                fp = str(list(set(found_port)))
                fp = fp.translate(None, "\'[]")

                c = str(cs)
                c = c.translate(None, "\'[]")
                port[0] = port[0].replace('(',"")
                port[0] = port[0].rstrip(',')
                self.csv_write.writerow([self.counter,self.ss,str(sorted_sec).translate(None,"[]"),fp,'','port',port[0],port[1].upper(),port[2],self.comp_name,'3','-',int(c.split(',')[0]) + no])
                self.counter += 1
                del sec_split[:]

            # ----------------------------------------------------------------------  ENTITY ---------------------------------------------------------------------

    def findEntityName(self):
        for i, entity in enumerate(self.entities):
            for j, token in enumerate(self.tokens):
                if entity == token and not self.tokens[j + 1][1] == 'body' and not self.tokens[j + 1][1] == 'body;':
                    self.tokens[j + 1][1] = self.tokens[j + 1][1].translate(None, ";\t\r\n")
                    self.found_entity_names.append([self.tokens[j][1], self.tokens[j + 1][1], self.tokens[j][0]])
                if entity == token and self.tokens[j + 1][1] == 'body':
                    self.tokens[j + 1][1] = self.tokens[j + 1][1].translate(None, ";\t\r\n")
                    self.tokens[j][1] += ' body'
                    self.found_entity_names.append([self.tokens[j][1], self.tokens[j + 2][1], self.tokens[j][0]])
                if entity == token and self.tokens[j + 1][1] == 'body;':
                    pass

    def findEndEntityName(self):
        for i, end in enumerate(self.ends):
            for j, token in enumerate(self.tokens):
                if end == token and not end[1] == 'end;':
                    if not self.tokens[j + 1][1] == 'entity':
                        if (j+1) < len(self.tokens):
                            self.tokens[j + 1][1] = self.tokens[j + 1][1].replace(';library', '')
                            self.tokens[j + 1][1] = self.tokens[j + 1][1].translate(None, ";\t\r\n")
                            self.found_end_entity_names.append([end[1], self.tokens[j + 1][1], end[0]])

                    if self.tokens[j + 1][1] == 'entity' and not self.tokens[j + 2][1] == 'body':
                        if (j+2) < len(self.tokens):
                            self.tokens[j + 2][1] = self.tokens[j + 2][1].replace(';library', '')
                            self.tokens[j + 1][1] = self.tokens[j + 1][1].translate(None, ";\t\r\n")
                            tag = end[1] + ' entity'
                            self.found_end_entity_names.append([tag, self.tokens[j + 2][1], end[0]])

                    if self.tokens[j + 1][1] == 'entity' and self.tokens[j + 2][1] == 'body':
                        if (j+3) < len(self.tokens):
                            self.tokens[j + 3][1] = self.tokens[j + 3][1].replace(';library', '')
                            self.tokens[j + 1][1] = self.tokens[j + 1][1].translate(None, ";\t\r\n")
                            tag = end[1] + ' entity body'
                            self.found_end_entity_names.append([tag, self.tokens[j + 3][1], end[0]])
                    if end == token and not end[1] == 'end;':
                        if j + 3 < len(self.tokens):
                            if self.tokens[j + 1][1] == 'entity' and self.tokens[j + 2][1] == 'body' and self.tokens[j + 3][1] in ('library', ''):
                                special = 'end entity body;'
                                self.complicated_entity_ends.append([special, end[0]])


    def identifyEntityBlocks(self):
        for i, entity in enumerate(self.found_entity_names):
            for j, end in enumerate(self.found_end_entity_names):
                if entity[1] == end[1]:
                    self.ent_blocks.append([entity, end])

    def entityBlocks(self):
        for i, block in enumerate(self.ent_blocks):
            if i + 1 < len(self.ent_blocks):
                if self.ent_blocks[i][0][0] == self.ent_blocks[i + 1][0][0] and self.ent_blocks[i][0][1] == self.ent_blocks[i + 1][0][1] and self.ent_blocks[i][0][2] == self.ent_blocks[i + 1][0][2]:
                    if self.ent_blocks[i][0][0] == 'entity':
                        self.ent_blocks.remove(self.ent_blocks[i + 1])
                    if self.ent_blocks[i][0][0] == 'entity body':
                        self.ent_blocks.remove(self.ent_blocks[i])
                if self.ent_blocks[i][0][0] == 'entity' and self.ent_blocks[i + 1][0][0] == 'entity body' and self.ent_blocks[i][0][1] == self.ent_blocks[i + 1][0][1] and self.ent_blocks[i][1][1] == self.ent_blocks[i + 1][1][1]:
                    if not self.ent_blocks[i][0][2] == self.ent_blocks[i + 1][0][2] and self.ent_blocks[i][1][2] == self.ent_blocks[i + 1][1][2]:
                        self.a.append(self.ent_blocks[i + 1])
                        self.ent_blocks.remove(self.ent_blocks[i + 1])

        for c in self.complicated_entity_ends:
            pass

        for block in self.ent_blocks:
            self.b.append(block)

    def compareEntityAB(self):
        for a in self.a:
            for b in self.b:
                if a[0] == b[0]:
                    self.a.remove(a)

            for a in self.a:
                for b in self.b:
                    if a[0][0] == b[0][0] and a[0][1] == b[0][1]:
                        self.a.remove(a)
            self.c = self.a


    def finalEntityBlocks(self):
        for c in self.c:
            self.ent_blocks.append(c)

        for block in self.ent_blocks:
            pin_s = 0
            pin_e = 0

            if not len(block[1]) == 2:
                p1 = [block[0][1:]][0]
                p2 = [block[1][1:]][0]
                p1 = p1[::-1]
                p2 = p2[::-1]
                p1 = p1[0].split(' ')
                p2 = p2[0].split(' ')
                p1 = p1[3]
                p2 = p2[3]

                for i,token in enumerate(self.new_tokens):
                    if p1 == token[0]:
                        pin_s = i

                for i,token in enumerate(self.new_tokens):
                    if p2 == token[0]:
                        pin_e = i

                span = self.new_tokens[pin_s:pin_e]
                pn = []

                self.super_ent = block[0][1]
                for i,s in enumerate(span):
                    # ports inside entities
                    if s[1] == ':':
                        port_name = span[i-1][1]
                        port_name = port_name.replace('(',' ')
                        port_name = port_name.split(' ')
                        port_name = port_name[0]
                        port_name = "".join(port_name.split())

                        if span[i+1][1] == 'in' or span[i+1][1] == 'out' or span[i+1][1] == 'IN' or span[i+1][1] == 'OUT':

                            if span[i+2][1] == 'std_logic' or span[i+2][1] == 'STD_LOGIC' or span[i+2][1] == 'std_logic;' or span[i+2][1] == 'std_logic);':
                                self.width = '1'

                            if span[i+2][1] == 'std_logic_vector' or span[i+2][1] == 'STD_LOGIC_VECTOR' :
                                self.width = (span[i+3][1]).replace('(','')

                            if 'STD_LOGIC_VECTOR(' in span[i+2][1] or 'std_logic_vector(' in span[i+2][1]:
                                wid = span[i+2][1].split('-')
                                if not len(wid) == 1:
                                    self.width = wid[-1]
                                else:
                                    wid = span[i+2][1].split('(')
                                    self.width = wid[-1]


                            pn.append([port_name,span[i+1][1],s[0],self.width])
                            self.tmp = span[i+1][1]

                        if span[i-2][1].endswith(','):
                            pn.append([span[i-2][1],self.tmp,s[0],self.width])

                        if span[i-3][1].endswith(','):
                            pn.append([span[i-3][1],self.tmp,s[0],self.width])

                        if span[i-4][1].endswith(','):
                            pn.append([span[i-4][1],self.tmp,s[0],self.width])

                        if span[i-5][1].endswith(','):
                            pn.append([span[i-5][1],self.tmp,s[0],self.width])

                        if span[i-6][1].endswith(','):
                            pn.append([span[i-5][1],self.tmp,s[0],self.width])


                self.entity_ports[self.super_ent] = pn

            else:
                for i,token in enumerate(self.new_tokens):
                    pass

    # -----------------------------------------------------  ENTITY ARCHITECTURE ---------------------------------------------------

    def findEntityArchName(self):

        for i,arch in enumerate(self.architectures):
            for j, token in enumerate(self.tokens):
                if arch == token:
                    self.tokens[j + 1][1] = self.tokens[j + 1][1].translate(None, ";\t\r\n")
                    self.tokens[j + 3][1] = self.tokens[j + 3][1].translate(None, ";\t\r\n")
                    self.found_entity_arch_names.append([self.tokens[j][1], self.tokens[j + 1][1],self.tokens[j + 3][1], self.tokens[j][0]])

        for fe in self.found_entity_arch_names:
            self.ent_name.append(fe[1])
        self.ent_name = list(set(self.ent_name))

    def findEndEntityArchName(self):
        for i, end in enumerate(self.ends):
            for j, token in enumerate(self.tokens):
                if end == token and self.tokens[j + 1][1] == 'architecture':
                    self.found_end_entity_arch_names.append(int(token[0].split(' ')[3]))

    def findEndEntityNameArch(self):
        for i,ent in enumerate(self.ent_name):
            for j,token in enumerate(self.tokens):
                if ent == token[1] and self.tokens[j-1][1] == 'end':
                    self.end_arch.append(int(token[0].split(' ')[3]))

        # line 7939 Yureka! I found it <-- needs to be removed
        for b in self.ent_blocks:
            if len(b[1]) > 2:
                self.clash.append(int(b[1][2].split(' ')[3]))

        self.end_arch = self.end_arch + self.found_end_entity_arch_names

        for c in self.clash:
            if c in self.end_arch:
                self.end_arch.remove(c)

        self.end_arch.sort()

    # -------------------------------------- creating master dictionary of flat hierarchy ----------------------------------

    def archSpan(self):
        #print self.end_arch
        #print len(self.end_arch)
        #print len(self.found_entity_arch_names)
        #print self.found_entity_arch_names
        for i,entity in enumerate(self.found_entity_arch_names):
            start = int(entity[3].split(' ')[3])
            end = self.end_arch[i]
            self.comp = {}
            self.gen, self.pro, self.fun = [], [], []
            self.c_span = []
            for j,tok in enumerate(self.new_tokens):
                if start < int(tok[0]) < end:
                    if tok[1] == 'component' and not self.new_tokens[j-1][1] == 'end':
                        self.c_span.append(tok[0])
                    if tok[1] == 'end' and self.new_tokens[j+1][1] == 'component;':
                        self.c_span.append(tok[0])
                    if tok[1] == 'end' and self.new_tokens[j+1][1] == 'component':
                        self.c_span.append(tok[0])

                    # generates with process inside
                    if tok[1] == 'end':
                        if (j+1) < len(self.new_tokens):
                            if self.new_tokens[j+1][1] == 'generate':
                                if self.new_tokens[j-2][1] == 'process' and self.new_tokens[j-3][1] == 'end':
                                    self.gen.append([self.new_tokens[j+2][1],self.new_tokens[j+2][0],self.new_tokens[j-1][1],self.new_tokens[j-1][0]])
                                if self.new_tokens[j-3][1] == 'process' and self.new_tokens[j-4][1] == 'end':
                                    self.gen.append([self.new_tokens[j+2][1],self.new_tokens[j+2][0],self.new_tokens[j-2][1],self.new_tokens[j-2][0]])
                                if self.new_tokens[j-5][1] == 'process' and self.new_tokens[j-6][1] == 'end':
                                    self.gen.append([self.new_tokens[j+2][1],self.new_tokens[j+2][0],self.new_tokens[j-4][1],self.new_tokens[j-4][0]])
                                else:
                                    self.gen.append([self.new_tokens[j+2][1],self.new_tokens[j+2][0],'',''])

                                # unique process
                    if tok[1] == 'end':
                        if (j+1) < len(self.new_tokens):
                            if self.new_tokens[j+1][1] == 'process' and not self.new_tokens[j+4] == 'generate' and not self.new_tokens[j+3] == 'end':
                                self.pro.append([self.new_tokens[j+2][1],self.new_tokens[j+2][0]])
                            if self.new_tokens[j+1][1] == 'process' and not self.new_tokens[j+5] == 'generate' and not self.new_tokens[j+4] == 'end':
                                self.pro.append([self.new_tokens[j+2][1],self.new_tokens[j+2][0]])
                            if self.new_tokens[j+1][1] == 'process' and not self.new_tokens[j+7] == 'generate' and not self.new_tokens[j+6] == 'end':
                                self.pro.append([self.new_tokens[j+2][1],self.new_tokens[j+2][0]])

                            # functions
                    if tok[1] == 'end':
                        if self.new_tokens[j+1][1] == 'function':
                            self.fun.append([self.new_tokens[j+2][1],self.new_tokens[j+2][0]])

            for i,num in enumerate(self.c_span):
                self.prt = {}
                if (i+1) < len(self.c_span):
                    for j,tok in enumerate(self.new_tokens):

                        if int(num) <= int(tok[0]) <= int(self.c_span[i+1]):
                            #ports:
                            if tok[1] == ':':
                                if self.new_tokens[j+1][1] == 'in' or self.new_tokens[j+1][1] == 'out' or self.new_tokens[j+1][1] == 'IN' or self.new_tokens[j+1][1] == 'OUT':
                                    self.port_io = self.new_tokens[j+1][1]

                                    if self.new_tokens[j+2][1] == 'std_logic' or self.new_tokens[j+2][1] == 'STD_LOGIC' or self.new_tokens[j+2][1] == 'std_logic;' or self.new_tokens[j+2][1] == 'std_logic);':
                                        self.port_width = '1'

                                    if self.new_tokens[j+2][1] == 'std_logic_vector' or self.new_tokens[j+2][1] == 'STD_LOGIC_VECTOR' :
                                        if str(self.new_tokens[j+3][1]).replace('(','').isdigit():
                                            self.port_width = int((self.new_tokens[j+3][1]).replace('(','')) + 1
                                            self.port_width = str(self.port_width)

                                    if 'STD_LOGIC_VECTOR(' in self.new_tokens[j+2][1] or 'std_logic_vector(' in self.new_tokens[j+2][1]:
                                        wid = self.new_tokens[j+2][1].split('-')
                                        if not len(wid) == 1:
                                            if str(wid[-1]).isdigit():
                                                self.port_width = int(wid[-1]) + 1
                                                self.port_width = str(self.port_width)

                                        else:
                                            wid = self.new_tokens[j+2][1].split('(')
                                            if str(wid[-1]).isdigit():
                                                self.port_width = int(wid[-1]) + 1
                                                self.port_width = str(self.port_width)

                                    self.prt[self.new_tokens[j-1][1].rstrip(',')] = self.new_tokens[j+1][0],self.port_io,self.port_width

                            if tok[1] == 'port(':
                                if self.new_tokens[j+1][1].endswith(','):
                                    self.prt[self.new_tokens[j+1][1].rstrip(',')] = self.new_tokens[j+1][0],self.port_io,self.port_width

                            if tok[1] == 'component' and not self.new_tokens[j-1][1] == 'end' and tok[0] == self.new_tokens[j+1][0] and not tok[0] == self.new_tokens[j-1][0]:
                                self.tem = self.new_tokens[j+1][1]
                                self.line = self.new_tokens[j+1][0]
                                self.comp[(self.tem,self.line)] = self.prt

            self.entity_generates[entity[2]] = self.gen
            self.entity_processes[entity[2]] = self.pro
            self.entity_functions[entity[2]] = self.fun
            self.master[(entity[2],entity[3].split(' ')[3])] = self.comp

    # -------------------------------------- creating in-depth hierarchy ----------------------------------

    def componentEntityLoc(self):
        for i,token in enumerate(self.new_tokens):
            if token[1] == 'entity' and not self.new_tokens[i-1][1] == 'end':
                self.cel[self.new_tokens[i+1][1].translate(None,'\t')] = self.new_tokens[i+1][0]


    def celMatch(self,x):
        for key,value in self.cel.iteritems():
            if key == x:
                self.loc = value
                return value

    # chopping forest of trees
    # condition => entity X component X => chop
    # condition => entity X not component X => Root

    #collecting all components name as a list

    def chopTress(self):
        for i,new_token in enumerate(self.new_tokens):
            if new_token[1] == 'component':
                pick = self.new_tokens[i+1][1].translate(None,";\t\n")
                pick = pick.replace('\r','')
                if not pick == 'component' or 'signal' or 'begin':
                    self.all_components.append(pick)
        self.all_components = list(set(self.all_components))

    def unRollMasterDict(self):
        for key,value in self.master.iteritems():
            for k,v in value.iteritems():
                print key[0] + '--->' + k[0]


    def inMaster(self,x):
        for key,value in self.master.iteritems():
            if x[0] == key[0]:
                self.out = key
                self.val = value
                return 1

    # Unrolling the master dictionary

    def Level_1_2_3(self):
        for entity,comports in sorted(self.master.iteritems(),key = lambda entity: entity[1], reverse = True):
            sec_split = []
            if not entity[0] in self.all_components:
                #print '==>' + entity[0]
                hints_fn = entity[0]
                if len(comports) > 1:
                    sec_ports = VHDLtoXml.vhdlSpecMapper(self,hints_fn)
                    for section in sec_ports[0]:
                        sec_split.append(section.split(' '))
                    sec = {}
                    for j,s in enumerate(sec_split):
                        sec[s[0]] = s[1]

                    sorted_sec = sorted(sec.iteritems(), key = operator.itemgetter(1),reverse = True)

                    if not len(sorted_sec) < 1 and not sorted_sec is None:
                        self.ss = sorted_sec[0][0]
                    else:
                        self.ss = ''

                    self.csv_write.writerow([self.counter,self.ss,str(sorted_sec).translate(None,"[]\""),'-','','entity',entity[0],'-','-','Root','1','-',entity[1]])
                    self.counter += 1

                    # printing entity ports

                    for key,value in self.entity_ports.iteritems():
                        sec_split = []
                        if key == entity[0]:
                            for v in value:
                                #print 'port ' + v[0]
                                found_port = []
                                hints_fn = v[0].rstrip(',')
                                hints = hints_fn.split('_')
                                sec_ports = VHDLtoXml.vhdlSpecMapper(self,hints_fn)
                                for section in sec_ports[0]:
                                    sec_split.append(section.split(' '))

                                sec = {}
                                for k,s in enumerate(sec_split):
                                    sec[s[0]] = s[1]

                                sorted_sec = sorted(sec.iteritems(), key = operator.itemgetter(1),reverse = True)
                                if not len(sorted_sec) < 1 and not sorted_sec is None:
                                    self.ss = sorted_sec[0][0]
                                else:
                                    self.ss = ''

                                sec_ports[1] = (list(set(sec_ports[1])))

                                for port in sec_ports[1]:
                                    if hints_fn == port:
                                        found_port.append(port)

                                first_ent = str(entity[0]).split('_')
                                for port in sec_ports[1]:
                                    if first_ent[0] in port:
                                        if hints[-1].lower() in port:
                                            found_port.append(port)

                                fp = str(list(set(found_port)))
                                fp = fp.replace('[','')
                                fp = fp.replace(']','')
                                fp = fp.replace('\'','')
                                fp = fp.rstrip(',')

                                self.csv_write.writerow([self.counter,self.ss,str(sorted_sec).translate(None,"[]\""),fp,'','port',v[0].translate(None,',;\t\r'),v[1].upper(),v[3],entity[0],'2','-',v[2]])
                                self.counter += 1
                                del sec_split[:]

                    for components,c_ports in comports.iteritems():
                        sec_split = []
                        if not components[0] == entity[0]:

                            #print '|' + 5 * '_' + components[0]

                            hints_fn = components[0]
                            sec_ports = VHDLtoXml.vhdlSpecMapper(self,hints_fn)
                            for section in sec_ports[0]:
                                sec_split.append(section.split(' '))
                            sec = {}
                            for i,s in enumerate(sec_split):
                                sec[s[0]] = s[1]

                            sorted_sec = sorted(sec.iteritems(), key = operator.itemgetter(1),reverse = True)
                            if not len(sorted_sec) < 1 and not sorted_sec is None:
                                self.ss = sorted_sec[0][0]
                            else:
                                self.ss = ''

                            if VHDLtoXml.celMatch(self,components[0]):
                                self.csv_write.writerow([self.counter,self.ss,str(sorted_sec).translate(None,"[]\""),'-','','component',components[0].translate(None,',;\t\r'),'-','-',entity[0],'2',self.loc,components[1]])
                            else:
                                self.csv_write.writerow([self.counter,self.ss,str(sorted_sec).translate(None,"[]\""),'-','','component',components[0].translate(None,',;\t\r'),'-','-',entity[0],'2','-',components[1]])

                            del sec_split[:]
                            self.counter += 1
                            self.temp = components[0]


                            # printing ports of components

                            for key,value in c_ports.iteritems():
                                sec_split = []
                                found_port = []
                                hints_fn = key.rstrip(',')
                                hints = hints_fn.split('_')
                                #print 'port ' + hints_fn
                                sec_ports = VHDLtoXml.vhdlSpecMapper(self,hints_fn)
                                for section in sec_ports[0]:
                                    sec_split.append(section.split(' '))

                                sec = {}

                                for i,s in enumerate(sec_split):
                                    sec[s[0]] = s[1]

                                sorted_sec = sorted(sec.iteritems(), key = operator.itemgetter(1),reverse = True)

                                if not len(sorted_sec) < 1 and not sorted_sec is None:
                                    self.ss = sorted_sec[0][0]

                                else:
                                    self.ss = ''

                                sec_ports[1] = (list(set(sec_ports[1])))
                                first_ent = str(components[0]).split('_')

                                for port in sec_ports[1]:
                                    if hints_fn == port:
                                        found_port.append(port)

                                for port in sec_ports[1]:
                                    if first_ent[0] in port:
                                        if hints[-1].lower() in port:
                                            found_port.append(port)

                                fp = str(list(set(found_port)))
                                fp = fp.replace('[','')
                                fp = fp.replace(']','')
                                fp = fp.replace('\'','')
                                fp = fp.rstrip(',')


                                self.csv_write.writerow([self.counter,self.ss,str(sorted_sec).translate(None,"[]\""),fp,'','port',key.rstrip(',').translate(None,',;\t\r'),value[1],value[2],str(self.temp).translate(None,',;\t\r'),'3','-',value[0]])
                                self.counter += 1
                                del sec_split[:]

                            #printing generates
                            g_list = []
                            for key,value in self.entity_generates.iteritems():
                                if key == entity[0]:
                                    if not value == [] or not value is None:
                                        for v in value:
                                            if not v[2] == '':
                                                hints_fn = v[0].rstrip(';')
                                                sec_ports = VHDLtoXml.vhdlSpecMapper(self,hints_fn)

                                                for section in sec_ports[0]:
                                                    sec_split.append(section.split(' '))

                                                sec = {}

                                                for i,s in enumerate(sec_split):
                                                    sec[s[0]] = s[1]

                                                sorted_sec = sorted(sec.iteritems(), key = operator.itemgetter(1),reverse = True)

                                                if not len(sorted_sec) < 1 and not sorted_sec is None:
                                                    self.ss = sorted_sec[0][0]

                                                else:
                                                    self.ss = ''
                                                g_list.append([self.counter,self.ss,str(sorted_sec).translate(None,"[]\""),'-','-','generate',v[0].translate(None,',;\t\r'),'','',components[0],'3','-',v[1]])
                                                #self.csv_write.writerow([self.counter,self.ss,'-','-','generate',v[0],'','',components[0],'3',v[1]])
                                                #self.counter += 1
                                                del sec_split[:]

                                                # ------- process within the generate -------
                                                hints_fn = v[2].rstrip(';')
                                                sec_ports = VHDLtoXml.vhdlSpecMapper(self,hints_fn)


                                                for section in sec_ports[0]:
                                                    sec_split.append(section.split(' '))

                                                sec = {}

                                                for i,s in enumerate(sec_split):
                                                    sec[s[0]] = s[1]

                                                sorted_sec = sorted(sec.iteritems(), key = operator.itemgetter(1),reverse = True)

                                                if not len(sorted_sec) < 1 and not sorted_sec is None:
                                                    self.ss = sorted_sec[0][0]

                                                else:
                                                    self.ss = ''
                                                g_list.append([self.counter,self.ss,str(sorted_sec).translate(None,"[]\""),'-','-','process',v[2].translate(None,',;\t\r'),'','',v[0].translate(None,',;'),'4','-',v[3]])
                                                #self.csv_write.writerow([self.counter,self.ss,'-','-','process',v[2],'','',v[0],'4',v[3]])
                                                #self.counter += 1
                                                del sec_split[:]

                                            else:
                                                hints_fn = v[0].rstrip(';')
                                                sec_ports = VHDLtoXml.vhdlSpecMapper(self,hints_fn)

                                                for section in sec_ports[0]:
                                                    sec_split.append(section.split(' '))

                                                sec = {}

                                                for i,s in enumerate(sec_split):
                                                    sec[s[0]] = s[1]

                                                sorted_sec = sorted(sec.iteritems(), key = operator.itemgetter(1),reverse = True)

                                                if not len(sorted_sec) < 1 and not sorted_sec is None:
                                                    self.ss = sorted_sec[0][0]

                                                else:
                                                    self.ss = ''
                                                g_list.append([self.counter,self.ss,str(sorted_sec).translate(None,"[]\""),'-','-','generate',v[0].translate(None,',;\t\r'),'','',components[0],'3','-',v[1]])
                                                #self.csv_write.writerow([self.counter,self.ss,'-','-','generate',v[0],'','',components[0],'3',v[1]])
                                                #self.counter += 1
                                                del sec_split[:]

                            g_list = list(VHDLtoXml.unique_items(self,g_list))
                            for gl in g_list:
                                self.csv_write.writerow(gl)
                                self.counter += 1

                            #printing processes
                            p_list = []
                            for key,value in self.entity_processes.iteritems():
                                if key == entity[0]:
                                    if not value == [] or not value is None:
                                        for v in value:
                                            hints_fn = v[0].rstrip(';')
                                            sec_ports = VHDLtoXml.vhdlSpecMapper(self,hints_fn)

                                            for section in sec_ports[0]:
                                                sec_split.append(section.split(' '))

                                            sec = {}

                                            for i,s in enumerate(sec_split):
                                                sec[s[0]] = s[1]

                                            sorted_sec = sorted(sec.iteritems(), key = operator.itemgetter(1),reverse = True)

                                            if not len(sorted_sec) < 1 and not sorted_sec is None:
                                                self.ss = sorted_sec[0][0]

                                            else:
                                                self.ss = ''
                                            p_list.append([self.counter,self.ss,str(sorted_sec).translate(None,"[]\""),'-','-','process',v[0].translate(None,',;\t\r'),'','',components[0],'3','-',v[1]])
                                            #self.csv_write.writerow([self.counter,self.ss,'-','-','process',v[0],'','',components[0],'3',v[1]])
                                            #self.counter += 1
                                            del sec_split[:]

                            p_list = list(VHDLtoXml.unique_items(self,p_list))
                            for pl in p_list:
                                self.csv_write.writerow(pl)
                                self.counter += 1

                            #printing functions
                            f_list = []
                            for key,value in self.entity_functions.iteritems():
                                if key == entity[0]:
                                    if not value == [] or not value is None:
                                        for v in value:
                                            if not v[2] == '':
                                                hints_fn = v[0].rstrip(';')
                                                #hints = hints_fn.split('_')
                                                sec_ports = VHDLtoXml.vhdlSpecMapper(self,hints_fn)
                                                for section in sec_ports[0]:
                                                    sec_split.append(section.split(' '))

                                                sec = {}

                                                for i,s in enumerate(sec_split):
                                                    sec[s[0]] = s[1]

                                                sorted_sec = sorted(sec.iteritems(), key = operator.itemgetter(1),reverse = True)

                                                if not len(sorted_sec) < 1 and not sorted_sec is None:
                                                    self.ss = sorted_sec[0][0]

                                                else:
                                                    self.ss = ''
                                                f_list.append([self.counter,self.ss,str(sorted_sec).translate(None,"[]\""),'-','-','function',v[0].translate(None,',;\r\t'),'','',components[0],'3','-',v[1]])
                                                #self.csv_write.writerow([self.counter,self.ss,'-','-','function',v[0],'','',components[0],'3',v[1]])
                                                #self.counter += 1
                                                del sec_split[:]

                            f_list = list(VHDLtoXml.unique_items(self,f_list))
                            for fl in f_list:
                                self.csv_write.writerow(fl)
                                self.counter += 1

                            indent = 10
                            level = 3
                            VHDLtoXml.hierarchyTracer(self,components,indent + 5,level)


    def hierarchyTracer(self,x,ind,lev):
        sec_split = []
        if VHDLtoXml.inMaster(self,x):
            for key,value in self.val.iteritems():
                if len(value) > 0:
                    if not key[0] == x[0]:
                        #print '|' + ind * '_' + key[0]
                        hints_fn = key[0]
                        sec_ports = VHDLtoXml.vhdlSpecMapper(self,hints_fn)
                        for section in sec_ports[0]:
                            sec_split.append(section.split(' '))
                        sec = {}
                        for i,s in enumerate(sec_split):
                            sec[s[0]] = s[1]

                        sorted_sec = sorted(sec.iteritems(), key = operator.itemgetter(1),reverse = True)
                        if not len(sorted_sec) < 1 and not sorted_sec is None:
                            self.ss = sorted_sec[0][0]
                        else:
                            self.ss = ''
                        if VHDLtoXml.celMatch(self,key[0]):
                            self.csv_write.writerow([self.counter + 1, self.ss,str(sorted_sec).translate(None,"[]\""), '-', '', 'component', key[0].translate(None,';,\r\t'), '-', '-', x[0], lev,self.loc, key[1]])
                        else:
                            self.csv_write.writerow([self.counter + 1, self.ss,str(sorted_sec).translate(None,"[]\""), '-', '', 'component', key[0].translate(None,';,\r\t'), '-', '-', x[0], lev,'-', key[1]])
                        self.counter += 1
                        del sec_split[:]


                        VHDLtoXml.printPorts(self,value,lev,key[0],self.counter + 1)
                        VHDLtoXml.printGenerates(self,self.val,lev,key[0])
                        VHDLtoXml.printProcesses(self,self.val,lev,key[0])
                        VHDLtoXml.printFunctions(self,self.val,lev,key[0])
                        VHDLtoXml.hierarchyTracer(self,key,ind + 5,lev + 1)


    # printing ports
    def printPorts(self,x,lev,parent,counter):
        sec_split = []
        self.counter = counter
        for k,v in x.iteritems():
            found_port = []
            hints_fn = k.rstrip(';')
            hints = hints_fn.split('_')
            sec_ports = VHDLtoXml.vhdlSpecMapper(self,hints_fn)

            for section in sec_ports[0]:
                sec_split.append(section.split(' '))

            sec = {}

            for i,s in enumerate(sec_split):
                sec[s[0]] = s[1]

            sorted_sec = sorted(sec.iteritems(), key = operator.itemgetter(1),reverse = True)

            if not len(sorted_sec) < 1 and not sorted_sec is None:
                self.ss = sorted_sec[0][0]

            else:
                self.ss = ''

            sec_ports[1] = (list(set(sec_ports[1])))
            first_ent = str(parent).split('_')  # <== parent of port

            for port in sec_ports[1]:
                if hints_fn == port:
                    found_port.append(port)

            for port in sec_ports[1]:
                if first_ent[0] in port:
                    if hints[-1].lower() in port:
                        found_port.append(port)

            fp = str(list(set(found_port)))
            fp = fp.translate(None,'[]\'')
            self.csv_write.writerow([self.counter,self.ss,str(sorted_sec).translate(None,"[]\""),fp,'','port',k.translate(None,';,\r\t'),v[1],v[2],parent,lev + 1,'-',v[0]])
            self.counter += 1
            del sec_split[:]


    def printGenerates(self,x,lev,parent):
        sec_split = []
        gen_list = []

        # printing Generates
        for key,value in self.entity_generates.iteritems():
            if key == parent:
                if not value == [] or not value is None:
                    for v in value:
                        if not v[2] == '':
                            hints_fn = v[0].rstrip(';')
                            sec_ports = VHDLtoXml.vhdlSpecMapper(self,hints_fn)

                            for section in sec_ports[0]:
                                sec_split.append(section.split(' '))

                            sec = {}

                            for i,s in enumerate(sec_split):
                                sec[s[0]] = s[1]

                            sorted_sec = sorted(sec.iteritems(), key = operator.itemgetter(1),reverse = True)

                            if not len(sorted_sec) < 1 and not sorted_sec is None:
                                self.ss = sorted_sec[0][0]

                            else:
                                self.ss = ''

                            gen_list.append([self.counter,self.ss,str(sorted_sec).translate(None,"[]\""),'-','-','generate',v[0].translate(None,';,\r\t'),'-','-',parent,'3','-',v[1]])
                            #self.csv_write.writerow([self.counter,self.ss,'-','-','generate',v[0],'-','-',parent,'3',v[1]])
                            #self.counter += 1
                            del sec_split[:]

                            # ------- process within the generate -------

                            hints_fn = v[2].rstrip(';')
                            sec_ports = VHDLtoXml.vhdlSpecMapper(self,hints_fn)

                            for section in sec_ports[0]:
                                sec_split.append(section.split(' '))

                            sec = {}

                            for i,s in enumerate(sec_split):
                                sec[s[0]] = s[1]

                            sorted_sec = sorted(sec.iteritems(), key = operator.itemgetter(1))

                            if not len(sorted_sec) < 1 and not sorted_sec is None:
                                self.ss = sorted_sec[0][0]

                            else:
                                self.ss = ''

                            gen_list.append([self.counter,self.ss,str(sorted_sec).translate(None,"[]\""),'-','-','process',v[2].translate(None,';,\r\t'),'-','-',v[0],'4','-',v[3]])
                            #self.csv_write.writerow([self.counter,self.ss,'-','-','process',v[2],'-','-',v[0],'4',v[3]])
                            #self.counter += 1
                            del sec_split[:]

                        else:
                            hints_fn = v[0].rstrip(';')
                            sec_ports = VHDLtoXml.vhdlSpecMapper(self,hints_fn)

                            for section in sec_ports[0]:
                                sec_split.append(section.split(' '))

                            sec = {}

                            for i,s in enumerate(sec_split):
                                sec[s[0]] = s[1]

                            sorted_sec = sorted(sec.iteritems(), key = operator.itemgetter(1),reverse = True)

                            if not len(sorted_sec) < 1 and not sorted_sec is None:
                                self.ss = sorted_sec[0][0]

                            else:
                                self.ss = ''
                            gen_list.append([self.counter,self.ss,str(sorted_sec).translate(None,"[]\""),'-','-','generate',v[0].translate(None,';,\r\t'),'-','-',parent,'3','-',v[1]])
                            #self.csv_write.writerow([self.counter,self.ss,'-','-','generate',v[0],'-','-',parent,'3',v[1]])
                            #self.counter += 1
                            del sec_split[:]


        gen_list = list(VHDLtoXml.unique_items(self,gen_list))
        for g in gen_list:
            self.csv_write.writerow(g)
            self.counter += 1

    def printProcesses(self,x,lev,parent):
        sec_split = []
        pro_list = []
        # printing processes

        for key,value in self.entity_processes.iteritems():
            if key == parent:
                if not value == [] or not value is None:
                    for v in value:
                        hints_fn = v[0].rstrip(';')
                        sec_ports = VHDLtoXml.vhdlSpecMapper(self,hints_fn)

                        for section in sec_ports[0]:
                            sec_split.append(section.split(' '))

                        sec = {}

                        for i,s in enumerate(sec_split):
                            sec[s[0]] = s[1]

                        sorted_sec = sorted(sec.iteritems(), key = operator.itemgetter(1),reverse = True)

                        if not len(sorted_sec) < 1 and not sorted_sec is None:
                            self.ss = sorted_sec[0][0]

                        else:
                            self.ss = ''
                        pro_list.append([self.counter,self.ss,str(sorted_sec).translate(None,"[]\""),'-','-','process',v[0].translate(None,';,\r\t'),'-','-',parent,'3','-',v[1]])
                        #self.csv_write.writerow([self.counter,self.ss,'-','-','process',v[0],'-','-',parent,'3',v[1]])
                        #self.counter += 1
                        del sec_split[:]

        pro_list = list(VHDLtoXml.unique_items(self,pro_list))
        for p in pro_list:
            self.csv_write.writerow(p)
            self.counter += 1

    def printFunctions(self,x,lev,parent):
        sec_split = []
        fun_list = []
        # printing functions
        for key,value in self.entity_functions.iteritems():
            if key == parent:
                if not value == [] or not value is None:
                    for v in value:

                        hints_fn = v[0].rstrip(';')
                        sec_ports = VHDLtoXml.vhdlSpecMapper(self,hints_fn)

                        for section in sec_ports[0]:
                            sec_split.append(section.split(' '))

                        sec = {}

                        for i,s in enumerate(sec_split):
                            sec[s[0]] = s[1]

                        sorted_sec = sorted(sec.iteritems(), key = operator.itemgetter(1),reverse = True)

                        if not len(sorted_sec) < 1 and not sorted_sec is None:
                            self.ss = sorted_sec[0][0]

                        else:
                            self.ss = ''
                        fun_list.append([self.counter,self.ss,str(sorted_sec).translate(None,"[]\""),'-','-','function',v[0].translate(None,';,\r\t'),'','',parent,'3','-',v[1]])
                        #self.csv_write.writerow([self.counter,self.ss,'-','-','function',v[0],'','',parent,'3',v[1]])
                        #self.counter += 1
                        del sec_split[:]

        fun_list = list(VHDLtoXml.unique_items(self,fun_list))
        for f in fun_list:
            self.csv_write.writerow(f)
            self.counter += 1

    # --------------------------------------- finding closest section using location-vectors and proximity weighing -------------------------------

    # last two positions of location vectors are neglected | stmt & word
    # depth of search = 15

    def checkLevel_1_1_Match(self,x):
        self.s = []
        del x[-2:]
        for s in self.secs:
            y = s[1].split(' ')
            del y[-2:]
            if x == y:
                self.s.append(s[0])
        return self.s

    def checkLevel_1_2_Match(self,x):
        self.s = []
        del x[-3:]
        for s in self.secs:
            y = s[1].split(' ')
            del y[-2:]
            if x == y:
                self.s.append(s[0])
        return self.s

    def checkLevel_1_3_Match(self,x):
        self.s = []
        del x[-4:]
        for s in self.secs:
            y = s[1].split(' ')
            del y[-2:]
            if x == y:
                self.s.append(s[0])
        return self.s

    def checkLevel_1_4_Match(self,x):
        self.s = []
        del x[-5:]
        for s in self.secs:
            y = s[1].split(' ')
            del y[-2:]
            if x == y:
                self.s.append(s[0])
        return self.s

    def checkLevel_1_5_Match(self,x):
        self.s = []
        del x[-6:]
        for s in self.secs:
            y = s[1].split(' ')
            del y[-2:]
            if x == y:
                self.s.append(s[0])
        return self.s

    def checkLevel_2_1_Match(self,x):
        self.s = []
        del x[-2:]
        for s in self.secs:
            y = s[1].split(' ')
            del y[-3:]
            if x == y:
                self.s.append(s[0])
        return self.s

    def checkLevel_2_2_Match(self,x):
        self.s = []
        del x[-3:]
        for s in self.secs:
            y = s[1].split(' ')
            del y[-3:]
            if x == y:
                self.s.append(s[0])
        return self.s

    def checkLevel_2_3_Match(self,x):
        self.s = []
        del x[-4:]
        for s in self.secs:
            y = s[1].split(' ')
            del y[-3:]
            if x == y:
                self.s.append(s[0])
        return self.s

    def checkLevel_2_4_Match(self,x):
        self.s = []
        del x[-5:]
        for s in self.secs:
            y = s[1].split(' ')
            del y[-3:]
            if x == y:
                self.s.append(s[0])
        return self.s

    def checkLevel_2_5_Match(self,x):
        self.s = []
        del x[-6:]
        for s in self.secs:
            y = s[1].split(' ')
            del y[-3:]
            if x == y:
                self.s.append(s[0])
        return self.s

    def checkLevel_3_1_Match(self,x):
        self.s = []
        del x[-2:]
        for s in self.secs:
            y = s[1].split(' ')
            del y[-4:]
            if x == y:
                self.s.append(s[0])
        return self.s

    def checkLevel_3_2_Match(self,x):
        self.s = []
        del x[-3:]
        for s in self.secs:
            y = s[1].split(' ')
            del y[-4:]
            if x == y:
                self.s.append(s[0])
        return self.s

    def checkLevel_3_3_Match(self,x):
        self.s = []
        del x[-4:]
        for s in self.secs:
            y = s[1].split(' ')
            del y[-4:]
            if x == y:
                self.s.append(s[0])
        return self.s

    def checkLevel_3_4_Match(self,x):
        self.s = []
        del x[-5:]
        for s in self.secs:
            y = s[1].split(' ')
            del y[-4:]
            if x == y:
                self.s.append(s[0])
        return self.s

    def checkLevel_3_5_Match(self,x):
        self.s = []
        del x[-6:]
        for s in self.secs:
            y = s[1].split(' ')
            del y[-2:]
            if x == y:
                self.s.append(s[0])
        return self.s

    def vhdlSpecMapper(self,hints_fn):
        sections = []
        mapped_port = []
        section_and_ports = []
        hints_fn = hints_fn.translate(None, "\t\r\n") # double check for false positives
        if hints_fn.lower() in self.clean_words.keys() and len(hints_fn) > 1:
            value = self.clean_words.get(hints_fn.lower())
            if not len(value) > 1:
                pins_1_1  = value[0].split(' ')
                matched_sections = VHDLtoXml.checkLevel_1_1_Match(self, pins_1_1)
                for section in matched_sections:
                    sections.append(section + ' 1.0')
                mapped_port.append(hints_fn.lower())
            else:
                for val in value:
                    pins_1_1 = val.split(' ')
                    matched_sections = VHDLtoXml.checkLevel_1_1_Match(self,pins_1_1)
                    for section in matched_sections:
                        sections.append(section + ' 1.0')
                    mapped_port.append(hints_fn.lower())

            if not len(value) > 1:
                pins_1_2  = value[0].split(' ')
                matched_sections = VHDLtoXml.checkLevel_1_2_Match(self,pins_1_2)
                for section in matched_sections:
                    sections.append(section + ' 0.99')
                mapped_port.append(hints_fn.lower())
            else:
                for val in value:
                    pins_1_2 = val.split(' ')
                    matched_sections = VHDLtoXml.checkLevel_1_2_Match(self,pins_1_2)
                    for section in matched_sections:
                        sections.append(section + ' 0.99')
                    mapped_port.append(hints_fn.lower())

            if not len(value) > 1:
                pins_1_3  = value[0].split(' ')
                matched_sections = VHDLtoXml.checkLevel_1_3_Match(self,pins_1_3)
                for section in matched_sections:
                    sections.append(section + ' 0.98')
                mapped_port.append(hints_fn.lower())
            else:
                for val in value:
                    pins_1_3 = val.split(' ')
                    matched_sections = VHDLtoXml.checkLevel_1_3_Match(self,pins_1_3)
                    for section in matched_sections:
                        sections.append(section + ' 0.98')
                    mapped_port.append(hints_fn.lower())

            if not len(value) > 1:
                pins_1_4  = value[0].split(' ')
                matched_sections = VHDLtoXml.checkLevel_1_4_Match(self,pins_1_4)
                for section in matched_sections:
                    sections.append(section + ' 0.97')
                mapped_port.append(hints_fn.lower())
            else:
                for val in value:
                    pins_1_4 = val.split(' ')
                    matched_sections = VHDLtoXml.checkLevel_1_4_Match(self,pins_1_4)
                    for section in matched_sections:
                        sections.append(section + ' 0.97')
                    mapped_port.append(hints_fn.lower())

            if not len(value) > 1:
                pins_1_5  = value[0].split(' ')
                matched_sections = VHDLtoXml.checkLevel_1_5_Match(self,pins_1_5)
                for section in matched_sections:
                    sections.append(section + ' 0.96')
                mapped_port.append(hints_fn.lower())
            else:
                for val in value:
                    pins_1_5 = val.split(' ')
                    matched_sections = VHDLtoXml.checkLevel_1_5_Match(self,pins_1_5)
                    for section in matched_sections:
                        sections.append(section + ' 0.96')
                    mapped_port.append(hints_fn.lower())

            if not len(value) > 1:
                pins_2_1  = value[0].split(' ')
                matched_sections = VHDLtoXml.checkLevel_2_1_Match(self,pins_2_1)
                for section in matched_sections:
                    sections.append(section + ' 0.95')
                mapped_port.append(hints_fn.lower())
            else:
                for val in value:
                    pins_2_1 = val.split(' ')
                    matched_sections = VHDLtoXml.checkLevel_2_1_Match(self,pins_2_1)
                    for section in matched_sections:
                        sections.append(section + ' 0.95')
                    mapped_port.append(hints_fn.lower())

            if not len(value) > 1:
                pins_2_2  = value[0].split(' ')
                matched_sections = VHDLtoXml.checkLevel_2_2_Match(self,pins_2_2)
                for section in matched_sections:
                    sections.append(section + ' 0.94')
                mapped_port.append(hints_fn.lower())
            else:
                for val in value:
                    pins_2_2 = val.split(' ')
                    matched_sections = VHDLtoXml.checkLevel_2_2_Match(self,pins_2_2)
                    for section in matched_sections:
                        sections.append(section + ' 0.94')
                    mapped_port.append(hints_fn.lower())

            if not len(value) > 1:
                pins_2_3  = value[0].split(' ')
                matched_sections = VHDLtoXml.checkLevel_2_3_Match(self,pins_2_3)
                for section in matched_sections:
                    sections.append(section + ' 0.93')
                mapped_port.append(hints_fn.lower())
            else:
                for val in value:
                    pins_2_3 = val.split(' ')
                    matched_sections = VHDLtoXml.checkLevel_2_3_Match(self,pins_2_3)
                    for section in matched_sections:
                        sections.append(section + ' 0.93')
                    mapped_port.append(hints_fn.lower())

            if not len(value) > 1:
                pins_2_4  = value[0].split(' ')
                matched_sections = VHDLtoXml.checkLevel_2_4_Match(self,pins_2_4)
                for section in matched_sections:
                    sections.append(section + ' 0.92')
                mapped_port.append(hints_fn.lower())
            else:
                for val in value:
                    pins_2_4 = val.split(' ')
                    matched_sections = VHDLtoXml.checkLevel_2_4_Match(self,pins_2_4)
                    for section in matched_sections:
                        sections.append(section + ' 0.92')
                    mapped_port.append(hints_fn.lower())

            if not len(value) > 1:
                pins_2_5  = value[0].split(' ')
                matched_sections = VHDLtoXml.checkLevel_2_5_Match(self,pins_2_5)
                for section in matched_sections:
                    sections.append(section + ' 0.91')
                mapped_port.append(hints_fn.lower())
            else:
                for val in value:
                    pins_2_5 = val.split(' ')
                    matched_sections = VHDLtoXml.checkLevel_2_5_Match(self,pins_2_5)
                    for section in matched_sections:
                        sections.append(section + ' 0.91')
                    mapped_port.append(hints_fn.lower())

            if not len(value) > 1:
                pins_3_1  = value[0].split(' ')
                matched_sections = VHDLtoXml.checkLevel_3_1_Match(self,pins_3_1)
                for section in matched_sections:
                    sections.append(section + ' 0.90')
                mapped_port.append(hints_fn.lower())
            else:
                for val in value:
                    pins_3_1 = val.split(' ')
                    matched_sections = VHDLtoXml.checkLevel_3_1_Match(self,pins_3_1)
                    for section in matched_sections:
                        sections.append(section + ' 0.90')
                    mapped_port.append(hints_fn.lower())

            if not len(value) > 1:
                pins_3_2  = value[0].split(' ')
                matched_sections = VHDLtoXml.checkLevel_3_2_Match(self,pins_3_2)
                for section in matched_sections:
                    sections.append(section + ' 0.89')
                mapped_port.append(hints_fn.lower())
            else:
                for val in value:
                    pins_3_2 = val.split(' ')
                    matched_sections = VHDLtoXml.checkLevel_3_2_Match(self,pins_3_2)
                    for section in matched_sections:
                        sections.append(section + ' 0.89')
                    mapped_port.append(hints_fn.lower())

            if not len(value) > 1:
                pins_3_3  = value[0].split(' ')
                matched_sections = VHDLtoXml.checkLevel_3_3_Match(self,pins_3_3)
                for section in matched_sections:
                    sections.append(section + ' 0.88')
                mapped_port.append(hints_fn.lower())
            else:
                for val in value:
                    pins_3_3 = val.split(' ')
                    matched_sections = VHDLtoXml.checkLevel_3_3_Match(self,pins_3_3)
                    for section in matched_sections:
                        sections.append(section + ' 0.88')
                    mapped_port.append(hints_fn.lower())

            if not len(value) > 1:
                pins_3_4  = value[0].split(' ')
                matched_sections = VHDLtoXml.checkLevel_3_4_Match(self,pins_3_4)
                for section in matched_sections:
                    sections.append(section + ' 0.87')
                mapped_port.append(hints_fn.lower())
            else:
                for val in value:
                    pins_3_4 = val.split(' ')
                    matched_sections = VHDLtoXml.checkLevel_3_4_Match(self,pins_3_4)
                    for section in matched_sections:
                        sections.append(section + ' 0.87')
                    mapped_port.append(hints_fn.lower())

            if not len(value) > 1:
                pins_3_5  = value[0].split(' ')
                matched_sections = VHDLtoXml.checkLevel_3_5_Match(self,pins_3_5)
                for section in matched_sections:
                    sections.append(section + ' 0.86')
                mapped_port.append(hints_fn.lower())
            else:
                for val in value:
                    pins_3_5 = val.split(' ')
                    matched_sections = VHDLtoXml.checkLevel_3_5_Match(self,pins_3_5)
                    for section in matched_sections:
                        sections.append(section + ' 0.86')
                    mapped_port.append(hints_fn.lower())

    # ****************************** finding partial matches ***************************
        else:
            for key, value in self.clean_words.iteritems():
                m = SequenceMatcher(lambda x: x == "_", hints_fn.lower(), key.lower())
                if m.ratio() > .60 and len(hints_fn) > 1: # threshold for character matching set to 0.60 (60 %)
                    cf = round(m.ratio(),2)
                    if not len(value) > 1:
                        pins_1_1  = value[0].split(' ')
                        matched_sections = VHDLtoXml.checkLevel_1_1_Match(self,pins_1_1)
                        for section in matched_sections:
                            sections.append(section + ' ' + str(cf))
                        mapped_port.append(key)

                    else:
                        for val in value:
                            pins_1_1 = val.split(' ')
                            matched_sections = VHDLtoXml.checkLevel_1_1_Match(self,pins_1_1)
                            for section in matched_sections:
                                sections.append(section + ' ' + str(cf))
                            mapped_port.append(key)

                    if not len(value) > 1:
                        pins_1_2  = value[0].split(' ')
                        matched_sections = VHDLtoXml.checkLevel_1_2_Match(self,pins_1_2)
                        for section in matched_sections:
                            sections.append(section + ' ' + str(cf))
                        mapped_port.append(key)
                    else:
                        for val in value:
                            pins_1_2 = val.split(' ')
                            matched_sections = VHDLtoXml.checkLevel_1_2_Match(self,pins_1_2)
                            for section in matched_sections:
                                sections.append(section + ' ' + str(cf))
                            mapped_port.append(key)

                    if not len(value) > 1:
                        pins_1_3  = value[0].split(' ')
                        matched_sections = VHDLtoXml.checkLevel_1_3_Match(self,pins_1_3)
                        for section in matched_sections:
                            sections.append(section + ' ' + str(cf))
                        mapped_port.append(key)
                    else:
                        for val in value:
                            pins_1_3 = val.split(' ')
                            matched_sections = VHDLtoXml.checkLevel_1_3_Match(self,pins_1_3)
                            for section in matched_sections:
                                sections.append(section + ' ' + str(cf))
                            mapped_port.append(key)

                    if not len(value) > 1:
                        pins_1_4  = value[0].split(' ')
                        matched_sections = VHDLtoXml.checkLevel_1_4_Match(self,pins_1_4)
                        for section in matched_sections:
                            sections.append(section + ' ' + str(cf))
                        mapped_port.append(key)
                    else:
                        for val in value:
                            pins_1_4 = val.split(' ')
                            matched_sections = VHDLtoXml.checkLevel_1_4_Match(self,pins_1_4)
                            for section in matched_sections:
                                sections.append(section + ' ' + str(cf))
                            mapped_port.append(key)

                    if not len(value) > 1:
                        pins_2_1 = value[0].split(' ')
                        matched_sections = VHDLtoXml.checkLevel_2_1_Match(self,pins_2_1)
                        for section in matched_sections:
                            sections.append(section + ' ' + str(cf))
                        mapped_port.append(key)
                    else:
                        for val in value:
                            pins_2_1 = val.split(' ')
                            matched_sections = VHDLtoXml.checkLevel_2_1_Match(self,pins_2_1)
                            for section in matched_sections:
                                sections.append(section + ' ' + str(cf))
                            mapped_port.append(key)

                    if not len(value) > 1:
                        pins_2_2  = value[0].split(' ')
                        matched_sections = VHDLtoXml.checkLevel_2_2_Match(self,pins_2_2)
                        for section in matched_sections:
                            sections.append(section + ' ' + str(cf))
                        mapped_port.append(key)
                    else:
                        for val in value:
                            pins_2_2 = val.split(' ')
                            matched_sections = VHDLtoXml.checkLevel_2_2_Match(self,pins_2_2)
                            for section in matched_sections:
                                sections.append(section + ' ' + str(cf))
                            mapped_port.append(key)

                    if not len(value) > 1:
                        pins_2_3  = value[0].split(' ')
                        matched_sections = VHDLtoXml.checkLevel_2_3_Match(self,pins_2_3)
                        for section in matched_sections:
                            sections.append(section + ' ' + str(cf))
                        mapped_port.append(key)
                    else:
                        for val in value:
                            pins_2_3 = val.split(' ')
                            matched_sections = VHDLtoXml.checkLevel_2_3_Match(self,pins_2_3)
                            for section in matched_sections:
                                sections.append(section + ' ' + str(cf))
                            mapped_port.append(key)

                    if not len(value) > 1:
                        pins_2_4  = value[0].split(' ')
                        matched_sections = VHDLtoXml.checkLevel_2_4_Match(self,pins_2_4)
                        for section in matched_sections:
                            sections.append(section + ' ' + str(cf))
                        mapped_port.append(key)
                    else:
                        for val in value:
                            pins_2_4 = val.split(' ')
                            matched_sections = VHDLtoXml.checkLevel_2_4_Match(self,pins_2_4)
                            for section in matched_sections:
                                sections.append(section + ' ' + str(cf))
                            mapped_port.append(key)

                    if not len(value) > 1:
                        pins_3_1  = value[0].split(' ')
                        matched_sections = VHDLtoXml.checkLevel_3_1_Match(self,pins_3_1)
                        for section in matched_sections:
                            sections.append(section + ' ' + str(cf))
                        mapped_port.append(key)
                    else:
                        for val in value:
                            pins_3_1 = val.split(' ')
                            matched_sections = VHDLtoXml.checkLevel_3_1_Match(self,pins_3_1)
                            for section in matched_sections:
                                sections.append(section + ' ' + str(cf))
                            mapped_port.append(key)

                    if not len(value) > 1:
                        pins_3_2  = value[0].split(' ')
                        matched_sections = VHDLtoXml.checkLevel_3_2_Match(self,pins_3_2)
                        for section in matched_sections:
                            sections.append(section + ' ' + str(cf))
                        mapped_port.append(key)
                    else:
                        for val in value:
                            pins_3_2 = val.split(' ')
                            matched_sections = VHDLtoXml.checkLevel_3_2_Match(self,pins_3_2)
                            for section in matched_sections:
                                sections.append(section + ' ' + str(cf))
                            mapped_port.append(key)

                    if not len(value) > 1:
                        pins_3_3  = value[0].split(' ')
                        matched_sections = VHDLtoXml.checkLevel_3_3_Match(self,pins_3_3)
                        for section in matched_sections:
                            sections.append(section + ' ' + str(cf))
                        mapped_port.append(key)
                    else:
                        for val in value:
                            pins_3_3 = val.split(' ')
                            matched_sections = VHDLtoXml.checkLevel_3_3_Match(self,pins_3_3)
                            for section in matched_sections:
                                sections.append(section + ' ' + str(cf))
                            mapped_port.append(key)

                    if not len(value) > 1:
                        pins_3_4  = value[0].split(' ')
                        matched_sections = VHDLtoXml.checkLevel_3_4_Match(self,pins_3_4)
                        for section in matched_sections:
                            sections.append(section + ' ' + str(cf))
                        mapped_port.append(key)
                    else:
                        for val in value:
                            pins_3_4 = val.split(' ')
                            matched_sections = VHDLtoXml.checkLevel_3_4_Match(self,pins_3_4)
                            for section in matched_sections:
                                sections.append(section + ' ' + str(cf))
                            mapped_port.append(key)

        section_and_ports.append([sections, mapped_port])
        return section_and_ports[0]

