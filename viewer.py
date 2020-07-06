# Name:         viewer.py
# Package:      wx.lib.pdfviewer
#
# Purpose:      A PDF report viewer class
#
# Author:       David Hughes     dfh@forestfield.co.uk
# Copyright:    Forestfield Software Ltd
# Licence:      Same as wxPython host

# History:      Created 17 Jun 2009
#
#               08 Oct 2011, Michael Hipp    michael@redmule.com
#               Added prompt, printer_name, orientation options to
#               pdfViewer.Print(). Added option to pdfViewer.LoadFile() to
#               accept a file-like object as well as a path string
#               Chris Johnson, Significant additions but some require modded pypdf2 
#               rolled in 3.7 changes to remove wx.NewId  
# Tags:         phoenix-port, documented, unittest
#  decode parms added 
#----------------------------------------------------------------------------

"""

This module provides the :class:`~wx.lib.pdfviewer.viewer.pdfViewer` to view PDF
files.
"""

import sys
import os
import time
import types
import copy
import shutil
from six import BytesIO, string_types

import wx

VERBOSE = True

try:
    # see http://pythonhosted.org/PyMuPDF - documentation & installation
    import fitz
    mupdf = True
    if VERBOSE: print('pdfviewer using PyMuPDF (GPL)')
except ImportError:
    mupdf = False
    try:
        # see http://pythonhosted.org/PyPDF2
        import PyPDF2
        from PyPDF2 import PdfFileReader
        from PyPDF2.pdf import ContentStream, PageObject
        from PyPDF2.filters import ASCII85Decode, FlateDecode , LZWDecode, CCITTFaxDecode  
        if VERBOSE: print('pdfviewer using PyPDF2')
    except ImportError:
        msg = "PyMuPDF or PyPDF2 must be available to use pdfviewer"
        raise ImportError(msg)

GraphicsContext = wx.GraphicsContext
have_cairo = False
if not mupdf:
    try:
        import wx.lib.wxcairo as wxcairo
        import cairo
        from wx.lib.graphics import GraphicsContext
        have_cairo = True
        if VERBOSE: print('pdfviewer using Cairo')
    except ImportError:
        if VERBOSE: print('pdfviewer using wx.GraphicsContext')

    # New PageObject method added by Forestfield Software
    def extractOperators(self):
        """
        Locate and return all commands in the order they
        occur in the content stream
        """
        ops = []
        content = self["/Contents"].getObject()
        if not isinstance(content, ContentStream):
            content = ContentStream(content, self.pdf)
        for op in content.operations:
            if type(op[1] == bytes):
                op = (op[0], op[1].decode())
            ops.append(op)
        return ops
    # Inject this method into the PageObject class
    PageObject.extractOperators = extractOperators

    # If reportlab is installed, use its stringWidth metric. For justifying text,
    # where widths are cumulative, dc.GetTextExtent consistently underestimates,
    # possibly because it returns integer rather than float.
    try:
        from reportlab.pdfbase.pdfmetrics import stringWidth
        have_rlwidth = True
        if VERBOSE: print('pdfviewer using reportlab stringWidth function')
    except ImportError:
        have_rlwidth = False

#----------------------------------------------------------------------------

class pdfViewer(wx.ScrolledWindow):
    """
    View pdf file in a scrolled window.  Contents are read from PDF file
    and rendered in a GraphicsContext. Show visible window contents
    as quickly as possible then, when using pyPDF, read the whole file and build
    the set of drawing commands for each page. This can take time for a big file or if
    there are complex drawings eg. ReportLab's colour shading inside charts and a
    progress bar can be displayed by setting self.ShowLoadProgress = True (default)
    """
    def __init__(self, parent, nid, pos, size, style):

        """
        Default class constructor.

        :param wx.Window `parent`: parent window. Must not be ``None``;
        :param integer `nid`: window identifier. A value of -1 indicates a default value;
        :param `pos`: the control position. A value of (-1, -1) indicates a default position,
         chosen by either the windowing system or wxPython, depending on platform;
        :type `pos`: tuple or :class:`wx.Point`
        :param `size`: the control size. A value of (-1, -1) indicates a default size,
         chosen by either the windowing system or wxPython, depending on platform;
        :type `size`: tuple or :class:`wx.Size`
        :param integer `style`: the button style (unused);

        """
        print( 'ssstarting viewer ...' )
        wx.ScrolledWindow.__init__(self, parent, nid, pos, size,
                                style | wx.NO_FULL_REPAINT_ON_RESIZE)
        self.SetBackgroundStyle(wx.BG_STYLE_CUSTOM)     # recommended in wxWidgets docs
        self.buttonpanel = None     # reference to panel is set by their common parent
        self._showLoadProgress = (not mupdf)

        self.Bind(wx.EVT_PAINT, self.OnPaint)
        self.Bind(wx.EVT_SIZE, self.OnResize)
        self.Bind(wx.EVT_SCROLLWIN, self.OnScroll)
        self.Bind(wx.EVT_IDLE, self.OnIdle)
        self.have_file = False
        self.resizing = False
        self.numpages = None
        self.zoomscale = -1     # fit page to screen width
        self.nom_page_gap = 20  # nominal inter-page gap (points)
        self.scrollrate = 20    # pixels per scrollbar increment
        self.page_buffer_valid = False
        self.page_after_zoom_change = None
        self.ClearBackground()

    def OnIdle(self, event):
        """
        Redraw on resize.
        """
        if self.resizing:
            self.page_buffer_valid = False
            self.Render()
            self.resizing = False
        event.Skip()

    def OnResize(self, event):
        """
        Buffer size change due to client area resize.
        """
        self.resizing = True
        event.Skip()

    def OnScroll(self, event):
        """
        Recalculate and redraw visible area. CallAfter is *essential*
        for coordination.
        """
        wx.CallAfter(self.Render)
        event.Skip()

    def OnPaint(self, event):
        """
        Refresh visible window with bitmap contents.
        """
        paintDC = wx.PaintDC(self)
        paintDC.Clear()         # in case buffer now smaller than visible window
        if hasattr(self, 'pdc'):
            paintDC.Blit(0, 0, self.winwidth, self.winheight, self.pdc,
                                                     self.xshift, self.yshift)

#----------------------------------------------------------------------------

    # This section defines the externally callable methods:
    # LoadFile, Save, Print, SetZoom, and GoPage
    # also the getter and setter for ShowLoadProgress
    # that is only applicable if using PyPDF2

    def LoadFile(self, pdf_file):
        """
        Read pdf file. Assume all pages are same size, for now.

        :param `pdf_file`: can be either a string holding
        a filename path or a file-like object.
        """
        def create_fileobject(filename):
            """
            Create and return a file object with the contents of filename,
            only used for testing.
            """
            f = open(filename, 'rb')
            stream = f.read()
            return BytesIO(stream)

        self.pdfpathname = ''
        if isinstance(pdf_file, string_types):
            # a filename/path string, save its name
            self.pdfpathname = pdf_file
            # remove comment from next line to test using a file-like object
            # pdf_file = create_fileobject(pdf_file)
            
        global missing_fonts
        missing_fonts = []

        if mupdf:
            self.pdfdoc = mupdfProcessor(self, pdf_file)
        else:
            self.pdfdoc = pypdfProcessor(self, pdf_file, self.ShowLoadProgress)

        self.numpages = self.pdfdoc.numpages
        self.pagewidth = self.pdfdoc.pagewidth
        self.pageheight = self.pdfdoc.pageheight
        self.page_buffer_valid = False
        self.Scroll(0, 0)               # in case this is a re-LoadFile
        self.CalculateDimensions()      # to get initial visible page range
        # draw and display the minimal set of pages
        self.pdfdoc.DrawFile(self.frompage, self.topage)
        self.have_file = True
        # now draw full set of pages
        wx.CallAfter(self.pdfdoc.DrawFile, 0, self.numpages-1)

    def Save(self):
        "Save a copy of the pdf file if it was originally named"
        if self.pdfpathname:
            wild = "Portable document format (*.pdf)|*.pdf"
            dlg = wx.FileDialog(self, message="Save file as ...",
                                  wildcard=wild, style=wx.FD_SAVE | wx.FD_OVERWRITE_PROMPT)
            if dlg.ShowModal() == wx.ID_OK:
                pathname = dlg.GetPath()
                shutil.copy(self.pdfpathname, pathname)
            dlg.Destroy()

    def Print(self, prompt=True, printer_name=None, orientation=None):
        """
        Print the pdf.

        :param boolean `prompt`: show the print dialog to the user (True/False). If
         False, the print dialog will not be shown and the pdf will be printed
         immediately. Default: True.
        :param string `printer_name`: the name of the printer that is to
         receive the printout. Default: as set by the O/S.
        :param `orientation`: select the orientation (:class:`wx.PORTRAIT` or
         :class:`wx.LANDSCAPE`) for the printout. Default: as set by the O/S.
        """
        pdd = wx.PrintDialogData()
        pdd.SetMinPage(1)
        pdd.SetFromPage(1)
        pdd.SetMaxPage(self.numpages)
        pdd.SetToPage(self.numpages)
        pdata = pdd.GetPrintData()
        if printer_name:
            pdata.SetPrinterName(printer_name)
        if orientation:
            pdata.SetOrientation(orientation)
        # PrintData does not return actual PrintQuality - it can't as printer_name not known
        # but it defaults to wx.PRINT_QUALITY_HIGH, overriding user's own setting for the
        # printer. However calling SetQuality with a value of 0 seems to leave the printer
        # setting untouched
        pdata.SetQuality(0)
        printer = wx.Printer(pdd)
        printout = pdfPrintout('', self)
        if (not printer.Print(self, printout, prompt=prompt) and
                       printer.GetLastError() == wx.PRINTER_ERROR):
            dlg = wx.MessageDialog(self, 'Unable to perform printing',
                              'Printer' , wx.OK | wx.ICON_INFORMATION)
            dlg.ShowModal()
            dlg.Destroy()
        printout.Destroy()

    def SetZoom(self, zoomscale):
        """
        Positive integer or floating zoom scale will render the file at corresponding
        size where 1.0 is "actual" point size (1/72").
        -1 fits page width and -2 fits page height into client area
        Redisplay the current page(s) at the new size

        :param `zoomscale`: an integer or float

        """
        pagenow = self.frompage
        self.zoomscale = zoomscale
        self.page_buffer_valid = False
        # calling GoPage now will trigger rendering at the new size but the page location
        # will be calculated based on the old zoom scale - so save the required page number
        # and call GoPage again *after* rendering at the new size
        self.page_after_zoom_change = pagenow
        self.GoPage(pagenow)

    def GoPage(self, pagenum):
        """
        Go to page

        :param integer `pagenum`: go to the provided page number if it is valid

        """
        if pagenum > 0 and pagenum <= self.numpages:
            self.Scroll(0, pagenum*self.Ypagepixels/self.GetScrollPixelsPerUnit()[1] + 1)
        else:
            self.Scroll(0, 0)
        # calling Scroll sometimes doesn't raise wx.EVT_SCROLLWIN eg Windows 8 64 bit - so
        wx.CallAfter(self.Render)

    @property
    def ShowLoadProgress(self):
        """Property to control if file reading progress is shown (PyPDF2 only)"""
        return self._showLoadProgress

    @ShowLoadProgress.setter
    def ShowLoadProgress(self, flag):
        """Setter for showLoadProgress."""
        self._showLoadProgress = flag

#----------------------------------------------------------------------------

    # This section is concerned with rendering a sub-set of drawing commands on demand

    def CalculateDimensions(self):
        """
        Compute the required buffer sizes to hold the viewed rectangle and
        the range of pages visible. Set self.page_buffer_valid = False if
        the current set of rendered pages changes
        """
        self.frompage = 0
        self.topage = 0
        device_scale = wx.ClientDC(self).GetPPI()[0]/72.0   # pixels per inch/points per inch
        self.font_scale_metrics =  1.0
        self.font_scale_size = 1.0
        # for Windows only with wx.GraphicsContext the rendered font size is too big
        # in the ratio of screen pixels per inch to points per inch
        # and font metrics are too big in the same ratio for both for Cairo and wx.GC
        if wx.PlatformInfo[1] == 'wxMSW':
            self.font_scale_metrics = 1.0 / device_scale
            if not have_cairo:
                self.font_scale_size = 1.0 / device_scale

        self.winwidth, self.winheight = self.GetClientSize()
        if self.winheight < 100:
            print( 'window height to small to display ? ' )
            return
        self.Ypage = self.pageheight + self.nom_page_gap
        if self.zoomscale > 0.0:
            self.scale = self.zoomscale * device_scale
        else:
            if int(self.zoomscale) == -1:   # fit width
                self.scale = self.winwidth / self.pagewidth
            else:                           # fit page
                self.scale = self.winheight / self.pageheight
        if self.scale == 0.0: # this could happen if the window was not yet initialized
            self.scale = 1.0
        self.Xpagepixels = int(round(self.pagewidth*self.scale))
        self.Ypagepixels = int(round(self.Ypage*self.scale))

        # adjust inter-page gap so Ypagepixels is a whole number of scroll increments
        # and page numbers change precisely on a scroll click
        idiv = self.Ypagepixels/self.scrollrate
        nlo = idiv * self.scrollrate
        nhi = (idiv + 1) * self.scrollrate
        if nhi - self.Ypagepixels < self.Ypagepixels - nlo:
            self.Ypagepixels = nhi
        else:
            self.Ypagepixels = nlo
        self.page_gap = self.Ypagepixels/self.scale - self.pageheight

        self.maxwidth = max(self.winwidth, self.Xpagepixels)
        self.maxheight = max(self.winheight, self.numpages*self.Ypagepixels)
        self.SetVirtualSize((self.maxwidth, self.maxheight))
        self.SetScrollRate(self.scrollrate, self.scrollrate)

        xv, yv = self.GetViewStart()
        dx, dy = self.GetScrollPixelsPerUnit()
        self.x0, self.y0   = (xv * dx, yv * dy)
        self.frompage = int(min(self.y0/self.Ypagepixels, self.numpages-1))
        self.topage = int(min((self.y0+self.winheight-1)/self.Ypagepixels, self.numpages-1))
        self.pagebufferwidth = max(self.Xpagepixels, self.winwidth)
        self.pagebufferheight = (self.topage - self.frompage + 1) * self.Ypagepixels

        # Inform buttonpanel controls of any changes
        if self.buttonpanel:
            self.buttonpanel.Update(self.frompage, self.numpages,
                                      self.scale/device_scale)

        self.page_y0 = self.frompage * self.Ypagepixels
        self.page_x0 = 0
        self.xshift = self.x0 - self.page_x0
        self.yshift = self.y0 - self.page_y0
        if not self.page_buffer_valid:  # via external setting
            self.cur_frompage = self.frompage
            self.cur_topage = self.topage
        else:   # page range unchanged? whole visible area will always be inside page buffer
            if self.frompage != self.cur_frompage or self.topage != self.cur_topage:
                self.page_buffer_valid = False    # due to page buffer change
                self.cur_frompage = self.frompage
                self.cur_topage = self.topage
        return

    def Render(self):
        """
        Recalculate dimensions as client area may have been scrolled or resized.
        The smallest unit of rendering that can be done is the pdf page. So render
        the drawing commands for the pages in the visible rectangle into a buffer
        big enough to hold this set of pages. Force re-creating the page buffer
        only when client view moves outside it.
        With PyPDF2, use gc.Translate to render each page wrt the pdf origin,
        which is at the bottom left corner of the page.
        """
        if not self.have_file:
            return
        self.CalculateDimensions()
        if not self.page_buffer_valid:
            # Initialize the buffer bitmap.
            self.pagebuffer = wx.Bitmap(self.pagebufferwidth, self.pagebufferheight)
            self.pdc = wx.MemoryDC(self.pagebuffer)     # must persist

            gc = GraphicsContext.Create(self.pdc)       # Cairo/wx.GraphicsContext API

            # white background
            path = gc.CreatePath()
            path.AddRectangle(0, 0,
                                self.pagebuffer.GetWidth(), self.pagebuffer.GetHeight())
            gc.SetBrush(wx.WHITE_BRUSH)
            gc.FillPath(path)

            for pageno in range(self.frompage, self.topage+1):
                self.xpageoffset = 0 - self.x0
                self.ypageoffset = pageno*self.Ypagepixels - self.page_y0
                gc.PushState()
                if mupdf:
                    gc.Translate(self.xpageoffset, self.ypageoffset)
                    # scaling is done inside RenderPage
                else:

                    gc.Translate(self.xpageoffset, self.ypageoffset +
                                    self.pageheight*self.scale)
                    gc.Scale(self.scale, self.scale)
                self.pdfdoc.RenderPage(gc, pageno, scale=self.scale)
                # Show inter-page gap
                gc.SetBrush(wx.Brush(wx.Colour(180, 180, 180)))        #mid grey
                gc.SetPen(wx.TRANSPARENT_PEN)
                if mupdf:
                    gc.DrawRectangle(0, self.pageheight*self.scale,
                                 self.pagewidth*self.scale, self.page_gap*self.scale)
                else:
                    gc.DrawRectangle(0, 0, self.pagewidth, self.page_gap)
                gc.PopState()
            gc.PushState()
            gc.Translate(0-self.x0, 0-self.page_y0)
            self.RenderPageBoundaries(gc)
            gc.PopState()

        self.page_buffer_valid = True
        self.Refresh(0) # Blit appropriate area of new or existing page buffer to screen

        # ensure we stay on the same page after zoom scale is changed
        if self.page_after_zoom_change:
            self.GoPage(self.page_after_zoom_change)
            self.page_after_zoom_change = None

    def RenderPageBoundaries(self, gc):
        """
        Show non-page areas in grey.
        """
        gc.SetBrush(wx.Brush(wx.Colour(180, 180, 180)))        #mid grey
        gc.SetPen(wx.TRANSPARENT_PEN)
        gc.Scale(1.0, 1.0)
        extrawidth = self.winwidth - self.Xpagepixels
        if extrawidth > 0:
            gc.DrawRectangle(self.winwidth-extrawidth, 0, extrawidth, self.maxheight)
        extraheight = self.winheight - (self.numpages*self.Ypagepixels - self.y0)
        if extraheight > 0:
            gc.DrawRectangle(0, self.winheight-extraheight, self.maxwidth, extraheight)

#============================================================================

class mupdfProcessor(object):
    """
    Create an instance of this class to open a PDF file, process the contents of
    each page and render each one on demand using the GPL mupdf library, which is
    accessed via the python-fitz package bindings (version 1.9.1 or later)
    """
    def __init__(self, parent, pdf_file):
        """
        :param `pdf_file`: a File object or an object that supports the standard
        read and seek methods similar to a File object.
        Could also be a string representing a path to a PDF file.
        """
        self.parent = parent
        if isinstance(pdf_file, string_types):
            # a filename/path string, pass the name to fitz.open
            pathname = pdf_file
            self.pdfdoc = fitz.open(pathname)
        else:
            # assume it is a file-like object, pass the stream content to fitz.open
            # and a '.pdf' extension in pathname to identify the stream type
            pathname = 'fileobject.pdf'
            if pdf_file.tell() > 0:     # not positioned at start
                pdf_file.seek(0)
            stream = bytearray(pdf_file.read())
            self.pdfdoc = fitz.open(pathname, stream)

        self.numpages = self.pdfdoc.pageCount
        page = self.pdfdoc.loadPage(0)
        self.pagewidth = page.bound().width
        self.pageheight = page.bound().height
        self.page_rect = page.bound()
        self.zoom_error = False     #set if memory errors during render

    def DrawFile(self, frompage, topage):
        """
        This is a no-op for mupdf. Each page is scaled and drawn on
        demand during RenderPage directly via a call to page.getPixmap()
        """
        self.parent.GoPage(frompage)

    def RenderPage(self, gc, pageno, scale=1.0):
        " Render the set of pagedrawings into gc for specified page "
        page = self.pdfdoc.loadPage(pageno)
        matrix = fitz.Matrix(scale, scale)
        try:
            pix = page.getPixmap(matrix=matrix)   # MUST be keyword arg(s)
            if [int(v) for v in fitz.version[1].split('.')] >= [1,15,0]:
                bmp = wx.Bitmap.FromBuffer(pix.width, pix.height, pix.samples)
            else:
                bmp = wx.Bitmap.FromBufferRGBA(pix.width, pix.height, pix.samples)
            gc.DrawBitmap(bmp, 0, 0, pix.width, pix.height)
            self.zoom_error = False
        except (RuntimeError, MemoryError):
            if not self.zoom_error:     # report once only
                self.zoom_error = True
                dlg = wx.MessageDialog(self.parent, 'Out of memory. Zoom level too high?',
                              'pdf viewer' , wx.OK |wx.ICON_EXCLAMATION)
                dlg.ShowModal()
                dlg.Destroy()

#============================================================================

class pypdfProcessor(object):
    """
    Create an instance of this class to open a PDF file, process the contents of
    every page using PyPDF2 then render each one on demand
    """
    def __init__(self, parent, fileobj, showloadprogress):
        self.parent = parent
        self.showloadprogress = showloadprogress
        self.pdfdoc = PdfFileReader(fileobj)
        self.numpages = self.pdfdoc.getNumPages()
        page1 = self.pdfdoc.getPage(0)
        self.pagewidth = float(page1.mediaBox.getUpperRight_x())
        self.pageheight = float(page1.mediaBox.getUpperRight_y())
        self.pagedrawings = {}
        self.unimplemented = {}
        self.formdrawings = {}
        self.page = None
        self.gstate = None
        self.saved_state = None
        self.knownfont = False
        self.progbar = None

    # These methods interpret the PDF contents as a set of drawing commands

    def Progress(self, ptype, value):
        " This function is called at regular intervals during Drawfile"
        if ptype == 'start':
            pmsg = 'Reading pdf file'
            self.progbar = wx.ProgressDialog('Load file', pmsg, value, None,
                         wx.PD_AUTO_HIDE|
                            wx.PD_ESTIMATED_TIME|wx.PD_REMAINING_TIME)
        elif ptype == 'progress':
            self.progbar.Update(value)
        elif ptype == 'end':
            self.progbar.Destroy()

    def DrawFile(self, frompage, topage):
        """
        Build set of drawing commands from PDF contents. Ideally these could be drawn
        straight into a PseudoDC and the visible section painted directly into
        scrolled window, but we need to be able to zoom and scale the output quickly
        without having to rebuild the drawing commands (slow). So build our
        own command lists, one per page, into self.pagedrawings.
        """
        numpages_generated = 0
        rp = (self.showloadprogress and frompage == 0 and topage == self.numpages-1)
        if rp: self.Progress('start', self.numpages)
        for pageno in range(frompage, topage+1):
            self.gstate = pdfState()    # state is reset with every new page
            self.saved_state = []
            self.page = self.pdfdoc.getPage(pageno)
            numpages_generated += 1
            pdf_fonts = self.FetchFonts(self.page)
            self.pagedrawings[pageno] = self.ProcessOperators(
                                    self.page.extractOperators(), pdf_fonts)
            if rp: self.Progress('progress', numpages_generated)

        if rp: self.Progress('end', None)
        self.parent.GoPage(frompage)

    def RenderPage(self, gc, pageno, scale=None):
        """
        Render the set of pagedrawings
        In a pdf file, bitmaps are treated as being of unit width and height and
        are scaled via a previous ConcatTransform containing the corresponding width
        and height as scale factors. wx.GraphicsContext/Cairo appear not to respond to
        this so scaling is removed from transform and width & height are added
        to the Drawbitmap call.
        """
        drawdict = {'ConcatTransform': gc.ConcatTransform,
                    'PushState': gc.PushState,
                    'PopState': gc.PopState,
                    'SetFont': gc.SetFont,
                    'SetPen': gc.SetPen,
                    'SetBrush': gc.SetBrush,
                    'DrawText': gc.DrawText,
                    'DrawBitmap': gc.DrawBitmap,
                    'CreatePath': gc.CreatePath,
                    'DrawPath': gc.DrawPath }
        print ( f'{pageno=}' )             
        for drawcmd, args, kwargs in self.pagedrawings[pageno]:
            # scale font if requested by printer DC
            if drawcmd == 'SetFont' and hasattr(gc, 'font_scale'):
                args[0].Scale(gc.font_scale)
            if drawcmd == 'ConcatTransform':
                cm = gc.CreateMatrix(*args, **kwargs)
                if VERBOSE: print( 'Concat transform ' , cm.Get() ) 
                args = (cm,)
            if drawcmd == 'CreatePath':
                gp = drawdict[drawcmd](*args, **kwargs)
                continue
            elif drawcmd == 'DrawPath':
                args = (gp, args[1])
            if drawcmd in drawdict:
                if drawdict == 'DrawBitmap' :
                    print( drawcmd , *args ) 
                try :    ## cjcj 2020-07    
                    drawdict[drawcmd](*args, **kwargs)
                except :
                   print( f'error with {drawcmd=}  {args} {kwargs} ' )
                   raise
                # reset font scaling in case RenderPage call is repeated
                if drawcmd == 'SetFont' and hasattr(gc, 'font_scale'):
                    args[0].Scale(1.0/gc.font_scale)
            else:
                pathdict = {'MoveToPoint': gp.MoveToPoint,
                            'AddLineToPoint': gp.AddLineToPoint,
                            'AddCurveToPoint': gp.AddCurveToPoint,
                            'AddRectangle': gp.AddRectangle,
                            'CloseSubpath': gp.CloseSubpath }
                if drawcmd in pathdict:
                    pathdict[drawcmd](*args, **kwargs)

    def FetchFonts(self, currentobject):
        " Return the standard fonts in current page or form"
        pdf_fonts = {}
        try:
            fonts = currentobject["/Resources"].getObject()['/Font']
            if fonts is not None :
                for key in fonts:
                    pdf_fonts[key] = fonts[key]['/BaseFont'][1:]     # remove the leading '/'
        except KeyError:
            pass
        except TypeError:    # None is not iterable
            pass
        return pdf_fonts

    def ProcessOperators(self, opslist, pdf_fonts):
        """
        Interpret each operation in opslist and return in drawlist.
        """
        drawlist = []
        path = []
        for operand, operator in opslist :
            g = self.gstate
            if operator == 'cm' and operand:        # new transformation matrix
                # some operands need inverting because directions of y axis
                # in pdf and graphics context are opposite
                a, b, c, d, e, f = [float(n) for n in operand]
                drawlist.append(['ConcatTransform', (a, -b, -c, d, e, -f), {}])
            elif operator == 'q':       # save state
                self.saved_state.append(copy.deepcopy(g))
                drawlist.append(['PushState', (), {}])
            elif operator == 'Q':       # restore state
                self.gstate = self.saved_state.pop()
                drawlist.append(['PopState', (), {}])
            elif operator == 'gs' :     # state from object
                gs_page_resources =  self.page["/Resources"].getObject()['/ExtGState']
                gs_resource  = self.gstate.LoadResource(  gs_page_resources[ operand[0] ]   )
             #  colour space 
            elif operator == 'CSxxx':      # Colour Space
                pass
            elif operator == 'RG':      # Stroke RGB
                rs, gs, bs = [int(float(n)*255) for n in operand]
                g.strokeRGB = wx.Colour(rs, gs, bs)
            elif operator == 'rg':      # Fill RGB
                rf, gf, bf = [int(float(n)*255) for n in operand]
                g.fillRGB = wx.Colour(rf, gf, bf)
            elif operator == 'K':       # Stroke CMYK
                rs, gs, bs = self.ConvertCMYK(operand)
                g.strokeRGB = wx.Colour(rs, gs, bs)
            elif operator == 'k':       # Fill CMYK
                rf, gf, bf = self.ConvertCMYK(operand)
                g.fillRGB = wx.Colour(rf, gf, bf)
            elif operator == 'G'  :      # Stroke Greyscale  0=black 1=white
                rs, gs, bs = self.ConvertGrey(operand) 
                g.strokeRGB = wx.Colour(rs, gs, bs)
            elif operator == 'g'  :      # Stroke Greyscale  0=black 1=white
                rf, gf, bf = self.ConvertGrey(operand) 
                g.fillRGB = wx.Colour(rf, gf, bf)
                
            elif operator == 'w':       # Line width
                g.lineWidth = max(float(operand[0]), 1.0)
            elif operator == 'J':       # Line cap
                ix = float(operand[0])
                g.lineCapStyle = {0: wx.CAP_BUTT, 1: wx.CAP_ROUND,
                                              2: wx.CAP_PROJECTING}[ix]
            elif operator == 'j':       # Line join
                ix = float(operand[0])
                g.lineJoinStyle = {0: wx.JOIN_MITER, 1: wx.JOIN_ROUND,
                                              2: wx.JOIN_BEVEL}[ix]
            elif operator == 'd':       # Line dash pattern
                g.lineDashArray = [int(n) for n in operand[0]]
                g.lineDashPhase = int(operand[1])
            elif operator in ('m', 'c', 'l', 're', 'v', 'y', 'h'):    # path defining ops
                NewClippingPathRequired = False
                path.append([[float(n) for n in operand], operator])
            elif operator in( 'W' ,'W*' ) :     # Clipping path
                '''
                In the middle of creating a graphics path (
                After  the path has been painted, the clipping path in the graphics state shall be set to 
                the intersection of the current clipping path and the newly constructed path. 
                '''
                NewClippingPathRequired = True
                NewClippingRule = operator
                
            elif operator in ('b', 'B', 'b*', 'B*', 'f', 'F', 'f*',
                                           's', 'S', 'n'):    # path drawing ops
                drawlist.extend(self.DrawPath(path, operator))
                if NewClippingPathRequired :
                    drawlist.extend( self.SetClippingPath( path , NewClippingRule) )
                    
                path = []
            elif operator == 'BT':      # begin text object
                g.textMatrix = [1, 0, 0, 1, 0, 0]
                g.textLineMatrix = [1, 0, 0, 1, 0, 0]
            elif operator == 'ET':      # end text object
                continue
            elif operator == 'Tm':      # text matrix
                g.textMatrix = [float(n) for n in operand]
                g.textLineMatrix = [float(n) for n in operand]
            elif operator == 'TL':      # text leading
                g.leading = float(operand[0])
            elif operator == 'Tc':     # character spacing
                g.charSpacing = float(operand[0])
            elif operator == 'Tw':      # word spacing
                g.wordSpacing = float(operand[0])
            elif operator == 'Tz':      # horizontal spacing percentg
                g.horizontalScaling = float(operand[0])/100
            elif operator == 'Ts':      # super/subscript
                g.textRise = float(operand[0])
            elif operator == 'Td':      # next line via offsets
                g.textLineMatrix[4] += float(operand[0])
                g.textLineMatrix[5] += float(operand[1])
                g.textMatrix = copy.copy(g.textLineMatrix)
            elif operator == 'Tf':      # text font
                g.font = pdf_fonts[operand[0]]
                g.fontSize = float(operand[1])
            elif operator == 'T*':      # next line via leading
                g.textLineMatrix[4] += 0
                g.textLineMatrix[5] -= g.leading if g.leading is not None else 0
                g.textMatrix = copy.copy(g.textLineMatrix)
            elif operator == 'Tj':      # show text
                
                operand[0] = operand[0].decode('latin-1').encode() 
                drawlist.extend(self.DrawTextString( operand[0] ))
            elif operator == "'" :      # equiv to T* and Tj 
                g.textLineMatrix[4] += 0
                g.textLineMatrix[5] -= g.leading if g.leading is not None else 0
                g.textMatrix = copy.copy(g.textLineMatrix)
                drawlist.extend(self.DrawTextString(
                                       operand[0].decode('latin-1')))
            elif operator == '"' :      # equiv to set word spacing, set character spacing T* and Tj 
                g.wordSpacing = float(operand[0])
                g.charSpacing = float(operand[1])
                g.textLineMatrix[4] += 0
                g.textLineMatrix[5] -= g.leading if g.leading is not None else 0
                g.textMatrix = copy.copy(g.textLineMatrix)
                drawlist.extend(self.DrawTextString(
                                       operand[2].decode('latin-1')))
            elif operator == 'TJ' :     # show text and spacing
                spacing = False
                for el in operand :
                    for e2 in el : 

                        if isinstance(e2 , PyPDF2.generic.NumberObject ) or isinstance(e2 , PyPDF2.generic.FloatObject ) :
                          # move back by n/1000 text units
                            #g.textLineMatrix[4] -= float(e2)*0.1
                            #g.textMatrix = copy.copy(g.textLineMatrix)
                            #g.textMatrix[4] -= float(e2)*0.1
                            #drawlist.extend(self.DrawTextString( b'' ) )

                            pass
                        else :     
                            
                            try:
                                drawlist.extend(self.DrawTextString( e2 ) )
                            except :
                                try:
                                    e3 = "?" * len(e2) 
                                    drawlist.extend(self.DrawTextString( e3 ) )
                                except:
                                    print( "TJ with odd operand {} of type {} ".format(e2, type(e2)))
                                pass
                if spacing:
                    print('PDF operator {} has spacing unimplemented (operand {})'.format(operator, operand))
            elif operator == 'Do':      # invoke named XObject
                dlist = self.InsertXObject(operand[0])
                if dlist:               # may be unimplemented decode
                    drawlist.extend(dlist)
            elif operator == 'INLINE IMAGE':    # special pyPdf case + operand is a dict
                dlist = self.InlineImage(operand)
                if dlist:               # may be unimplemented decode
                    drawlist.extend(dlist)
            else:                       # report once
                if operator not in self.unimplemented:
                    if VERBOSE: print(f'PDF {operator=} is not implemented  {operand=} ')
                    self.unimplemented[operator] = 1

        # Fix bitmap transform. Move the scaling from any transform matrix that precedes
        # a DrawBitmap operation into the op itself - the width and height extracted from
        # the bitmap is the size of the original PDF image not the size it is to be drawn
        
        # rotation and stretching need to be checked as may have swapped ratios
        
        for k in range(len(drawlist)-1):
            if drawlist[k][0] == 'ConcatTransform' and drawlist[k+1][0] == 'DrawBitmap':
                ctargs = list(drawlist[k][1])
                bmargs = list(drawlist[k+1][1])
                w = ctargs[0]
                h = ctargs[3]
                bmargs[2] = -ctargs[3]          # y position
                bmargs[3] = ctargs[0]           # width
                bmargs[4] = ctargs[3]           # height
                ctargs[0] = 1.0                 # 
                ctargs[1] = ctargs[1] / w       #  
                ctargs[2] = ctargs[2] / h         
                ctargs[3] = 1.0
                drawlist[k][1] = tuple(ctargs)
                drawlist[k+1][1] = tuple(bmargs)
        return drawlist

    def SetFont(self, pdfont, size):
        """
        Returns :class:`wx.Font` instance from supplied pdf font information.
        """
        global missing_fonts
        self.knownfont = True
        pdfont = pdfont.lower()
        if pdfont.count('courier'):
            family = wx.FONTFAMILY_MODERN
            font = 'Courier New'
        elif pdfont.count('helvetica'):
            family = wx.FONTFAMILY_SWISS
            font = 'Arial'
        elif pdfont.count('times'):
            family = wx.FONTFAMILY_ROMAN
            font = 'Times New Roman'
        elif pdfont.count('symbol'):
            family = wx.FONTFAMILY_DEFAULT
            font = 'Symbol'
        elif pdfont.count('zapfdingbats'):
            family = wx.FONTFAMILY_DEFAULT
            font = 'Wingdings'
        else:
            if pdfont in missing_fonts :
                pass
            else :
                missing_fonts.append( pdfont ) 
                if VERBOSE: print('Unknown font %s' % pdfont)
            self.knownfont = False
            family = wx.FONTFAMILY_SWISS
            font = 'Arial'

        weight = wx.FONTWEIGHT_NORMAL
        if pdfont.count('bold'):
            weight = wx.FONTWEIGHT_BOLD
        style = wx.FONTSTYLE_NORMAL
        if pdfont.count('oblique') or pdfont.count('italic'):
            style = wx.FONTSTYLE_ITALIC
        return wx.Font(max(1, size), family, style, weight, faceName=font)

    def DrawTextString(self, text):
        """
        Draw a text string. Word spacing only works for horizontal text.

        :param string `text`: the text to draw

        """
        dlist = []
        g = self.gstate
        f0  = self.SetFont(g.font, g.fontSize)
        f0.Scale(self.parent.font_scale_metrics)
        f1  = self.SetFont(g.font, g.fontSize)
        f1.Scale(self.parent.font_scale_size)
        
        dlist.append( ['SetFont', (f1, g.GetFillRGBA() ), {}])
        if g.wordSpacing > 0:
            textlist = text.split(b' ')
        else:
            textlist = [text,]
        for item in textlist:
            dlist.append(self.DrawTextItem(item, f0))
        return dlist

    def DrawTextSpace( self , adjust ) :
        
        dlist = []
        g = self.gstate
        f0  = self.SetFont(g.font, g.fontSize)
        f0.Scale(self.parent.font_scale_metrics)
        #print ( "font scale"  , f0.Scale() ) 
        f1  = self.SetFont(g.font, g.fontSize)
        f1.Scale(self.parent.font_scale_size)
        
        dlist.append(self.DrawTextItem(b'_', f0))
        return dlist
        

    def DrawTextItem(self, textitem, f):
        """
        Draw a text item.

        :param `textitem`: the item to draw
        :param `f`: the font to use for text extent measuring
        
        
        issue - the GetFullTextExtent only returns an integer 
        this means that text is not evenly spaced

        """
        dc = wx.ClientDC(self.parent)      # dummy dc for text extents
        g = self.gstate
        x = g.textMatrix[4]
        y = g.textMatrix[5] + g.textRise
        if g.wordSpacing > 0:
            textitem += b' '
        wid, ht, descend, x_lead = dc.GetFullTextExtent(textitem, f)
        if have_rlwidth and self.knownfont:   # use ReportLab stringWidth if available
            width = stringWidth(textitem, g.font, g.fontSize)
        else:
            width = wid
        g.textMatrix[4] += (width + g.wordSpacing)  # update current x position
        return ['DrawText', (textitem, x, -y-(ht-descend)), {}]

    def DrawPath(self, path, action):
        """
        Stroke and/or fill the defined path depending on operator.
        """
        dlist = []
        g = self.gstate
        acts = {'S':  (1, 0, 0),
                's':  (1, 0, 0),
                'f':  (0, 1, wx.WINDING_RULE),
                'F':  (0, 1, wx.WINDING_RULE),
                'f*': (0, 1, wx.ODDEVEN_RULE),
                'B':  (1, 1, wx.WINDING_RULE),
                'B*': (1, 1, wx.ODDEVEN_RULE),
                'b':  (1, 1, wx.WINDING_RULE),
                'b*': (1, 1, wx.ODDEVEN_RULE),
                'n':  (0, 0, 0) }
        stroke, fill, rule = acts[action]
        if action in ('s', 'b', 'b*'):
            path.append([[], 'h'])      # close path

        if stroke:
            if g.lineDashArray:
                style = wx.PENSTYLE_USER_DASH
            else:
                style = wx.PENSTYLE_SOLID
            cpen = wx.Pen(g.GetStrokeRGBA(), g.lineWidth, style)  # was g.strokeRGB cj
            cpen.SetCap(g.lineCapStyle)
            cpen.SetJoin(g.lineJoinStyle)
            if g.lineDashArray:
                cpen.SetDashes(g.lineDashArray)
            dlist.append(['SetPen', (cpen,), {}])
        else:
            dlist.append(['SetPen', (wx.TRANSPARENT_PEN,), {}])

        if fill :
            dlist.append(['SetBrush', (wx.Brush(g.GetFillRGBA()),), {}])
        else:
            dlist.append(['SetBrush', (wx.TRANSPARENT_BRUSH,), {}])

        dlist.append(['CreatePath', (), {}])
        for xylist, op in path:
            if op == 'm':           # move (to) current point
                x0 = xc = xylist[0]
                y0 = yc = -xylist[1]
                dlist.append(['MoveToPoint', (x0, y0), {}])
            elif op == 'l':         # draw line
                x2 = xylist[0]
                y2 = -xylist[1]
                dlist.append(['AddLineToPoint', (x2, y2), {}])
                xc = x2
                yc = y2
            elif op == 're':        # draw rectangle
                x = xylist[0]
                y = -xylist[1]
                w = xylist[2]
                h = xylist[3]
                retuple = (x, y-h, w, h)
                if h < 0.0:
                    retuple = (x, y, w, -h)
                dlist.append(['AddRectangle', retuple, {}])
            elif op in ('c', 'v', 'y'):         # draw Bezier curve
                args = []
                if op == 'v':
                    args.extend([xc, yc])
                args.extend([xylist[0], -xylist[1],
                                xylist[2], -xylist[3]])
                if op == 'y':
                    args.extend([xylist[2], -xylist[3]])
                if op == 'c':
                    args.extend([xylist[4], -xylist[5]])
                dlist.append(['AddCurveToPoint', args, {}])
            elif op == 'h':
                dlist.append(['CloseSubpath', (), {}])
        dlist.append(['DrawPath', ('GraphicsPath', rule), {}])
        return dlist
        
    def SetClippingPath(self, path, rule ):
        """
        Stroke and/or fill the defined path depending on operator.
        """
        print( 'Clipping paths not implemented' )
        dlist = []
        g = self.gstate
      
        if g.clippingPath == None :
            if VERBOSE : print( "clipping path is empty" )
            g.clippingPath = []
            
        g.clippingPath.append( path )
        g.ClippingRule = rule
        return dlist
       
    def InsertXObject(self, name):
        """
        XObject can be an image or a 'form' (an arbitrary PDF sequence).
        """
        dlist = []
        xobject = self.page["/Resources"].getObject()['/XObject']
        stream = xobject[name]
        if stream.get('/Subtype') == '/Form':
            # insert contents into current page drawing
            if VERBOSE: print( "Handling /Form ") 
            if not name in self.formdrawings:       # extract if not already done
                pdf_fonts = self.FetchFonts(stream)
                x_bbox = stream.get('/BBox')
                matrix = stream.get('/Matrix')
                form_ops = ContentStream(stream, self.pdfdoc).operations
                oplist = [([], 'q'), (matrix, 'cm')]    # push state & apply matrix
                oplist.extend(form_ops)                 # add form contents
                oplist.append(([], 'Q'))                # restore original state
                self.formdrawings[name] = self.ProcessOperators(oplist, pdf_fonts)
                if VERBOSE: print( f'Form has {len(form_ops)} operations ' ) 
            dlist.extend(self.formdrawings[name])
        elif stream.get('/Subtype') == '/Image':
            width = stream['/Width']
            height = stream['/Height']
            x_depth = stream['/BitsPerComponent']  
            x_size = width * height * x_depth / 8 
            x_color = stream[ '/ColorSpace' ]
            x_indexed = False
            x_palette = None
            try :
                if x_color is None :
                    if VERBOSE:  print( "Colour NOT indexed - in fact no colour at all" )                 
                elif "/Indexed" in x_color :
                    if VERBOSE: print( f"x_colour stream for indexed image {x_color} " )
                    xc = x_color
                    x_indexed = True
                    x_palette_size = x_color[2]
                    x_palette = x_color[3] 
                    if isinstance( x_palette , PyPDF2.generic.IndirectObject ):
                        x_palette = x_palette.getObject() 
                        if isinstance( x_palette , PyPDF2.generic.EncodedStreamObject ) :
                            x_palette = x_palette.getData() 
                    else :
                        if VERBOSE: print( "palette is in line " ) 
                    x_color = x_color[1]
                    if isinstance( x_color , PyPDF2.generic.IndirectObject ):
                        x_color = x_color.getObject() 
                else:
                    if VERBOSE:  print( "Colour NOT indexed" )                 
            except :
                if VERBOSE: print( 'Issue with indexed colour image stream->' , stream) 
                raise
                            
            filters = stream["/Filter"]
            decode_parms = stream[ "/DecodeParms" ]
            x_masked = stream.get("/Mask" )
            x_stencil = stream[ '/ImageMask'  ]
            
            compressed_length = len(stream._data) 
            print( f'compressed stream length {compressed_length} ' )
            data = self.UnpackImage( stream._data, filters, decode_parms)
            
            print( f"Image {x_color}   {width} x {height} x {x_depth} data length={len(data)} " )
            #JPEG image is self defining 
            if '/DCT' in filters or '/DCTDecode' in filters:
                istream = BytesIO(data)
                image = wx.Image(istream, wx.BITMAP_TYPE_JPEG)
                bitmap = wx.Bitmap(image)
                
            # Colour bit map is native 
            elif x_indexed == False and x_color == '/DeviceRGB' and x_depth == 8 :  
                try:
                    RGBdata = data
                    bitmap = wx.Bitmap.FromBuffer(width, height, data)   # RGB
                except:
                    print( 'Error creating bitmap w={} h={} data length {} (should be w x h x 3 )'.format(width,height,len(data) ) )
                
            elif  (x_color is None and x_depth != 1 ) :
                print( 'Unable to print image with no colour space unless 1 bit b&W' ) 
            
                      
            elif x_indexed and x_color == '/DeviceRGB' :
                RGBdata = self.DeindexImage( width , height, data, x_depth , x_palette_size , x_palette ) 
                bitmap = wx.Bitmap.FromBuffer(width, height, RGBdata) 
                
            elif x_indexed and x_color == '/DeviceGray' :
                rgb_palette = bytes( [3* x for x in palette ]) 
                RGBdata = self.DeindexImage( width , height, data, x_depth , x_palette_size , rgb_palette  ) 
                bitmap = wx.Bitmap.FromBuffer(width, height, RGBdata) 

            elif x_indexed :
                print( "Unable to deal with /Indexed colour space" , x_color  ) 
                print( "Bits {} Palette size {} Palette len {} ".format( x_depth , x_palette_size, len(x_palette) ) )
                print( x_palette , type( x_palette) )
                print("---------------" ) 
                         
            elif (x_color == '/DeviceGray' and x_depth in (1,2,4,8))  :
                if x_depth == 1 :
                    palette = bytes.fromhex( '000000FFFFFF' )
                elif x_depth == 2 :
                    palette = bytes.fromhex( '000000555555AAAAAAFFFFFF' )
                elif x_depth == 4 :
                    palette = bytes.fromhex( '000000111111222222333333444444555555666666777777'                           '888888999999AAAAAABBBBBBCCCCCCDDDDDDEEEEEEFFFFFF' )
                elif x_depth == 8 :
                    palette = bytes( [x for x in range(256) for z in range(3) ])
                else :
                    pass
                    
                palette_size = len(palette) 
                RGBdata = self.DeindexImage( width , height, data, x_depth , palette_size , palette  ) 
                bitmap = wx.Bitmap.FromBuffer(width, height, RGBdata) 
                
            elif (x_color is None and x_depth == 1 ) :  
                palette = bytes.fromhex( '000000FFFFFF' )

                #palette = bytes( [x for x in range(256) for z in range(3) ])
                palette_size = len(palette) 
                RGBdata = self.DeindexImage( width , height, data, x_depth , palette_size , palette  ) 
                bitmap = wx.Bitmap.FromBuffer(width, height, RGBdata) 
            
            elif  x_color == None:
                print( 'Unable to print image with no colour space' ) 
            
            else:
                print( '{} colour space is not implemented'.format( x_color ) )
                #elif x_color == '/DeviceCMYK' :
                #elif x_color == '/CalRCB' :
                #elif x_color == '/CalGray' :
                #elif x_color == '/Lab' :
                #elif x_color == '/ICCBased' :
                
            # Retrieve and apply Image Mask     
            if x_masked == None:
                pass
            elif  isinstance( x_masked , list)  : 
                print( 'Image is masked' )
                ck_bytes = bytes( bytearray( x_masked )  )
                
                ( r1,r9,g1,g9,b1,b9) = x_masked
                ck_key = bytes(bytearray( (r9,g9,b9) ))
                
                mask_data = self.FixColour( RGBdata , ck_bytes , ck_key)                 
                mask_bitmap = wx.Bitmap.FromBuffer(width, height, mask_data)
                mask = wx.Mask(mask_bitmap, wx.Colour( r9 , g9 , b9  )  )
                bitmap.SetMask(mask)

            else   : 
                x_mo     = stream["/Mask"].getObject()
                #print("     >" , x_mo                 )  
                filters, decode_parms
                mask_filters       = x_mo[ '/Filter']
                mask_decode_parms  = x_mo[ "/DecodeParms" ]
                mask_data = x_mo._data    
                mask_height        = x_mo[ '/Height' ]
                mask_width         = x_mo[ '/Width' ]
                    
                mask_data  = self.UnpackImage( mask_data , mask_filters, mask_decode_parms)
                #print(" mask data (length {} )".format(len(mask_data) ) , mask_data                ) 
                
                if True :
                    '''
                    the following code will change a 1 bit image to a 3 byte RGB black and white
                    by treating it as an indexed bitmap with a black and white pallete colours
                    '''
                    
                    palette = bytes.fromhex( '000000FFFFFF' )
                    palette_size = len(palette) 
                    mask_RGB = self.DeindexImage( mask_width, mask_height, mask_data, 1, palette_size , palette  ) 
                    #print( " RGB mask data length {}".format( len(mask_RGB)   ) )  
                    mask_bitmap = wx.Bitmap.FromBuffer(mask_width, mask_height, mask_RGB)
                    mask = wx.Mask(mask_bitmap, wx.WHITE )  
                    bitmap.SetMask(mask)
                else:
                    ''' 
                    we may alternativly be able to create a bitmap directly from the bits and use that
                    as a mask
                    '''
                    mask_bitmap = wx.Bitmap( mask_data, mask_height , mask_width , depth=1 )
                    mask = wx.Mask( mask_bitmap )
                    bitmap.SetMask(mask)
                    
            dlist.append(  ['DrawBitmap', (bitmap, 0, 0-height, width, height), {}] )
            return dlist


    def InlineImage(self, operand):
        """ operand contains an image"""
        dlist = []
        data = operand.get('data')
        settings = operand.get('settings')
        width = settings['/W']
        height = settings['/H']
        x_depth = settings['/BPC']
        filters = settings['/F']
        if '/DecodeParms'  in settings :
            decode_parms =  settings['/DecodeParms' ]
        elif '/DP' in settings :
            decode_parms =  settings['/DP' ]
        else:
            decode_parms = None 

        item = self.AddBitmap(data, width, height, filters,decode_parms )
        if item:            # may be unimplemented
            dlist.append(item)
        return dlist
    
    def UnpackImage(self , data , filters , decode_parms) :
        if '/LZWDecode' in filters :
            data = LZWDecode.decode(data)
        if '/A85' in filters or '/ASCII85Decode' in filters:
            data = ASCII85Decode.decode(data)
        if '/Fl' in filters or '/FlateDecode' in filters:
            data = FlateDecode.decode(data, None)
        if '/CCF' in filters or  '/CCITTFaxDecode' in filters:
            data = CCITTFaxDecode.decode(data, decodeParms=decode_parms)   
        #print( "data length {}".format(len(data)))   
        return data
        
    def FixColour(  self, RGBdata , colour_key_limits  , colour_key_fix) :
        """
        generate copy of RGB data with pixels replaced where it is within the limits 
        
        RGBData  8 bit RGB data (must have 3n bytes
        colour_key_limits      6 bytes  giving lower and upper ranges for RGB  e.g. R1 R9 G1 G9 B1 B9 
        colour_key_fix         3 bytes giving replacement colour
        
        """
        ( R1, R9, G1, G9, B1, B9) = bytearray( colour_key_limits)
        buffer = bytes( len( RGBdata ) )
        d2b = BytesIO(buffer ) 
        
        nfix = 0 
        pos = 0
        while pos < len( RGBdata ) :
            R = RGBdata[pos]
            G = RGBdata[pos+1]
            B = RGBdata[pos+2]
            
            if R >= R1 and R <= R9 and G >= G1 and G <= G9 and B >= B1 and B <= B9 :
               d2b.write( colour_key_fix ) 
               nfix += 1 
            else :
                d2b.write( RGBdata[pos:pos+3] ) 
            pos += 3
            
        d2b.seek(0)         
        d2 = d2b.getvalue()   
        d2b.close()
        del d2b 
        assert( len(RGBdata) == len(d2) )
        return d2
   
    def DeindexImage( self , width , height, data, x_depth , x_palette_size , x_palette , palette_chunk=3  )     :
        # 
        # for each input pel (of x_depth bits) find the corresponding n byte chunk in the palette and add it to the
        # output data.  The n chunk allows us to index RGB, CMYK or generate a 8bit mask 
        #  
        
        size = width * height * palette_chunk 
        buffer = bytes( size )
        d2b = BytesIO(buffer ) 
        if x_depth == 1 :
            for d in data :
                b8 = (d & 1 ) 
                b7 = (d & 2) >> 1
                b6 = (d & 4) >> 2
                b5 = (d & 8) >> 3
                b4 = (d & 16) >> 4
                b3 = (d & 32) >> 5
                b2 = (d & 64) >> 6
                b1 = (d & 128) >> 7
                d2b.write(x_palette[ b1 * palette_chunk : ( b1+1 ) * palette_chunk ]) 
                d2b.write(x_palette[ b2 * palette_chunk : ( b2+1 ) * palette_chunk ]) 
                d2b.write(x_palette[ b3 * palette_chunk : ( b3+1 ) * palette_chunk ]) 
                d2b.write(x_palette[ b4 * palette_chunk : ( b4+1 ) * palette_chunk ]) 
                d2b.write(x_palette[ b5 * palette_chunk : ( b5+1 ) * palette_chunk ]) 
                d2b.write(x_palette[ b6 * palette_chunk : ( b6+1 ) * palette_chunk ]) 
                d2b.write(x_palette[ b7 * palette_chunk : ( b7+1 ) * palette_chunk ]) 
                d2b.write(x_palette[ b8 * palette_chunk : ( b8+1 ) * palette_chunk ]) 
        elif x_depth  == 2 :
            for d in data :
                b4 = (d & 3  ) 
                b3 = (d & 12 >> 2 ) 
                b2 = (d & 48 >> 4 ) 
                b1 = (d & 192 >> 6 )
                d2b.write(x_palette[ b1 * palette_chunk : ( b1+1 ) * palette_chunk ]) 
                d2b.write(x_palette[ b2 * palette_chunk : ( b2+1 ) * palette_chunk ]) 
                d2b.write(x_palette[ b3 * palette_chunk : ( b3+1 ) * palette_chunk ]) 
                d2b.write(x_palette[ b4 * palette_chunk : ( b4+1 ) * palette_chunk ]) 
        elif x_depth  == 4  :       
            for d in data :
                b1 = (d & 15)  
                b2 = (d & 240) >> 4 
                d2b.write(x_palette[ b1 * palette_chunk : ( b1+1 ) * palette_chunk ]) 
                d2b.write(x_palette[ b2 * palette_chunk : ( b2+1 ) * palette_chunk ]) 
        elif x_depth  == 8  :       
            for d in data :
                b1 = (d)  
                d2b.write(x_palette[ b1 * palette_chunk : ( b1+1 ) * palette_chunk ]) 
                
        d2b.seek(0)         
        d2 = d2b.getvalue()   
        d2b.close()
        del d2b 
        return d2
        
    def AddBitmap(self , data, width, height, filters, decode_parms):
        """
        Add wx.Bitmap from data, processed by filters.
        """
        
        
        if '/LZWDecode' in filters :
            data = LZWDecode.decode(data)
        if '/A85' in filters or '/ASCII85Decode' in filters:
            data = ASCII85Decode.decode(data)
        if '/Fl' in filters or '/FlateDecode' in filters:
            data = FlateDecode.decode(data, decode_parms )
        if '/CCF' in filters or  '/CCITTFaxDecode' in filters:
            data = CCITTFaxDecode.decode(data, decodeParms=decode_parms)   
        
        if '/DCT' in filters or '/DCTDecode' in filters:
            stream = BytesIO(data)
            image = wx.Image(stream, wx.BITMAP_TYPE_JPEG)
            bitmap = wx.Bitmap(image)
        else:
            try:
                bitmap = wx.Bitmap.FromBuffer(width, height, data)   # RGB 
            except:
                
                from PIL import Image

                image = Image.frombytes(image_format, (width,height), data)
                print( "error" )
                
                return []       # any error
        return ['DrawBitmap', (bitmap, 0, 0-height, width, height), {}]

    def ConvertGrey( self, operand ):
        """
        Convert greyscale ( 0=Black 1=White) to nearest RGB.
        """
        r = round( operand[0] * 255) 
        g = round( operand[0] * 255) 
        b = round( operand[0] * 255) 
        return( r,g,b )
        
    def ConvertCMYK(self, operand):
        """
        Convert CMYK values (0 to 1.0) in operand to nearest RGB.
        """
        c, m, y, k = operand
        r = round((1-c)*(1-k)*255)
        b = round((1-y)*(1-k)*255)
        g = round((1-m)*(1-k)*255)
        return (r, g, b)

#----------------------------------------------------------------------------

class pdfState(object):
    """
    Instance holds the current pdf graphics and text state. It can be
    saved (pushed) and restored (popped) by the owning parent
    """
    def __init__ (self):
        """
        Creates an instance with default values. Individual attributes
        are modified directly not via getters and setters
        """
        self.lineWidth = 1.0
        self.lineCapStyle = wx.CAP_BUTT
        self.lineJoinStyle = wx.JOIN_MITER
        self.lineDashArray = []
        self.lineDashPhase = 0
        self.miterLimit = None
        self.automaticStrokeAdjustment = False 
        
        # these three only apply to printers
        self.overprint = False      #opaque (if true colours are merged ) 
        self.overprintNS = False
        self.overprintMode = 0 
        
        # 
        self.strokeTransparency = 1  # opaque
        self.strokeRGB = wx.Colour(0, 0, 0)
        
        self.fillTransparency = 1               # opaque
        self.fillRGB = wx.Colour(0, 0, 0)       # used for both shapes & text
        self.fillMode = None
        
        self.clippingPath = None 
        self.clippingRule = None 
        
        # The following variables relate to colour composition when an object is drawn over another
        # acrobat defines a series of standard modes for blending (similar to photoshop) 
        # and wx seems to just do the likewise but their models may differ
        # 
        # wx.COMPOSITION_INVALID 	Indicates invalid or unsupported composition mode.
        # wx.COMPOSITION_CLEAR 	R = 0
        # wx.COMPOSITION_SOURCE 	R = S
        # wx.COMPOSITION_OVER 	R = S + D*`(1 - `Sa)
        # wx.COMPOSITION_IN 	R = S* Da `
        # wx.COMPOSITION_OUT 	R = S*`(1 - `Da)
        # wx.COMPOSITION_ATOP 	R = S* Da + D*`(1 - `Sa)
        # wx.COMPOSITION_DEST 	R = D, essentially a noop
        # wx.COMPOSITION_DEST_OVER 	R = S*`(1 - `Da) + D
        # wx.COMPOSITION_DEST_IN 	R = D* Sa `
        # wx.COMPOSITION_DEST_OUT 	R = D*`(1 - `Sa)
        # wx.COMPOSITION_DEST_ATOP 	R = S*`(1 - `Da) + D* Sa `
        # wx.COMPOSITION_XOR 	R = S*`(1 - `Da) + D*`(1 - `Sa)
        # wx.COMPOSITION_ADD 	R = S + D



        self.textMatrix = [1, 0, 0, 1, 0, 0]
        self.textLineMatrix = [1, 0, 0, 1, 0, 0]
        self.charSpacing = 0
        self.wordSpacing = 0
        self.horizontalScaling = 1
        self.leading = None
        self.font = None
        self.fontSize = None
        self.textRenderMode = None
        self.textRise = 0
        
    def GetFillRGBA(self) :
        # applies the fill transparency to the fill RGB
        red    = self.fillRGB.Red()
        green  = self.fillRGB.Green()
        blue   = self.fillRGB.Blue()
        alpha  = self.fillTransparency * wx.ALPHA_OPAQUE 
        return wx.Colour(red, green , blue, alpha)   
        
    def GetStrokeRGBA(self) :
        # applies the fill transparency to the fill RGB
        red    = self.strokeRGB.Red()
        green  = self.strokeRGB.Green()
        blue   = self.strokeRGB.Blue()
        alpha  = self.strokeTransparency * wx.ALPHA_OPAQUE 
        return wx.Colour(red, green , blue, alpha)     

        
    def LoadResource( self , resource ) :
        '''Updates graphics state from /ExtGState page resource
        '''
        #xobject = self.page["/Resources"].getObject()['/ExtGState']
        #stream = xobject[name]
        
        if VERBOSE: print ( "Loading extended graphics state " , resource )
        
        for EGS in resource.keys() :
            EGV = resource.get( EGS )
            if EGS == '/Type' :
                 if EGV !=   '/ExtGState' :  
                    print(  "/ExtGState resource has bad /Type of {} ".format( EGV ) )
            elif EGS ==  "/SA" :
                self.automaticStrokeAdjustment = EGV 
            elif EGS ==  "/BM" :
                pass
            elif EGS ==  "/CA" :  # stroke transparency 0=transparent 1= opaque
                self.strokeTransparency = float(EGV)
            elif EGS ==  "/ca" :  # fill transparency 0=transparent 1= opaque
                self.fillTransparency = float(EGV)
            elif EGS ==  "/LW" :  # Line Width
                self.lineWidth = max(float(EGV), 1.0)
            elif EGS ==  "/LC" :  # Line Cap
                self.lineCapStyle = {0: wx.CAP_BUTT, 1: wx.CAP_ROUND, 2: wx.CAP_PROJECTING}[float(EGV)]
            elif EGS ==  "/LJ" :  # Line Join
                self.lineJoinStyle = {0: wx.JOIN_MITER, 1: wx.JOIN_ROUND, 2: wx.JOIN_BEVEL}[float(EGV)]
            elif EGS ==  "/ML" :  # Mitre Limit
                self.miterLimit = float(EGV)
            elif EGS ==  "/D" :  # Mitre Limit
                print(  "/ExtGState resource not properly handled yet {} {}".format( EGS , EGV ) )
                self.lineDashArray = EGV[0]
                self.lineDashPhase = EGV[1]
            elif EGS ==  "/RI" :  # intent
                print(  "/ExtGState resource not properly handled yet {} {}".format( EGS , EGV ) )
            elif EGS ==  "/OP" :  # Overprint (stroking) 
                self.overprint = EGV 
            elif EGS ==  "/op" :  # Overprint (non stroking) 
                self.overprintNS = EGV
            elif EGS ==  "/OPM" :  # Overprint Mode 
                self.overprintMode = EGV
            elif EGS ==  "/BG" :  # Black Generation 
                print(  "/ExtGState resource not properly handled yet {} {}".format( EGS , EGV ) )
            elif EGS ==  "/BG2" :  # Black Generation 
                print(  "/ExtGState resource not properly handled yet {} {}".format( EGS , EGV ) )
            elif EGS ==  "/TR" :  # Colour Mapping (color transfer)  
                print(  "/ExtGState resource not properly handled yet {} {}".format( EGS , EGV ) )
            elif EGS ==  "/TR2" :  # Colour Mapping (color transfer) 
                print(  "/ExtGState resource not properly handled yet {} {}".format( EGS , EGV ) )
            elif EGS ==  "/BG" :  # Black Generation 
                print(  "/ExtGState resource not properly handled yet {} {}".format( EGS , EGV ) )
            elif EGS ==  "/BG" :  # Black Generation 
                print(  "/ExtGState resource not properly handled yet {} {}".format( EGS , EGV ) )
            elif EGS ==  "/BG" :  # Black Generation 
                print(  "/ExtGState resource not properly handled yet {} {}".format( EGS , EGV ) )
            elif EGS ==  "/BG" :  # Black Generation 
                print(  "/ExtGState resource not properly handled yet {} {}".format( EGS , EGV ) )
            elif EGS ==  "/BG" :  # Black Generation 
                print(  "/ExtGState resource not properly handled yet {} {}".format( EGS , EGV ) )
            elif EGS ==  "/BG" :  # Black Generation 
                print(  "/ExtGState resource not properly handled yet {} {}".format( EGS , EGV ) )
            elif EGS ==  "/BG" :  # Black Generation 
                print(  "/ExtGState resource not properly handled yet {} {}".format( EGS , EGV ) )
            elif EGS ==  "/BM" :  # Bland Mode
                self.blendMode = EGV 

            else :
                print(  "/ExtGState unhandled variable {} value {}  ".format( EGS, EGV ) )
       
        #self.strokeRGB = wx.Colour(0, 0, 0)
        #self.fillRGB = wx.Colour(0, 0, 0)       # used for both shapes & text
                
        
        
#------------------------------------------------------------------------------

class pdfPrintout(wx.Printout):
    """
    Class encapsulating the functionality of printing out the document. The methods below
    over-ride those of the base class and supply document-specific information to the
    printing framework that calls them internally.
    """
    def __init__(self, title, view):
        """
        Pass in the instance of dpViewer to be printed.
        """
        wx.Printout.__init__(self, title)
        self.view = view

    def HasPage(self, pageno):
        """
        Report whether pageno exists.
        """
        if pageno <= self.view.numpages:
            return True
        else:
            return False

    def GetPageInfo(self):
        """
        Supply maximum range of pages and the range to be printed
        These are initial values passed to Printer dialog, where they
        can be amended by user.
        """
        maxnum = self.view.numpages
        return (1, maxnum, 1, maxnum)

    def OnPrintPage(self, page):
        """
        Provide the data for page by rendering the drawing commands
        to the printer DC, MuPDF returns the page content from an internally
        generated bitmap and sfac sets it to a high enough resolution that
        reduces anti-aliasing blur but keeps it small to minimise printing time
        """
        sfac = 1.0
        if mupdf:
            sfac = 4.0
        pageno = page - 1       # zero based
        width = self.view.pagewidth
        height = self.view.pageheight
        self.FitThisSizeToPage(wx.Size(width*sfac, height*sfac))
        dc = self.GetDC()
        gc = wx.GraphicsContext.Create(dc)
        if not mupdf:
            gc.Translate(0, height)
        if wx.PlatformInfo[1] == 'wxMSW' and have_cairo:
            if VERBOSE: print( 'Device scale adjusted for PPI' )
            device_scale = wx.ClientDC(self.view).GetPPI()[0]/72.0   # pixels per inch/ppi
            gc.font_scale = 1.0 / device_scale

        self.view.pdfdoc.RenderPage(gc, pageno, sfac)
        return True

