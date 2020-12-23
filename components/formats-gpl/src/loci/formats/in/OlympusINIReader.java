/*
 * #%L
 * OME Bio-Formats package for reading and converting biological file formats.
 * %%
 * Copyright (C) 2005 - 2016 Open Microscopy Environment:
 *   - Board of Regents of the University of Wisconsin-Madison
 *   - Glencoe Software, Inc.
 *   - University of Dundee
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 2 of the 
 * License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public 
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-2.0.html>.
 * #L%
 */

package loci.formats.in;

import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.InputStreamReader;
import java.io.IOException;
import java.io.File;
import java.io.ByteArrayOutputStream;
import java.util.ArrayList;
import java.util.List;
import java.util.HashMap;
import java.util.Collections;
import java.util.Comparator;
import java.text.DecimalFormat;
import java.lang.Math;

import loci.common.Constants;
import loci.common.IniList;
import loci.common.IniParser;
import loci.common.IniTable;
import loci.common.Location;
import loci.common.RandomAccessInputStream;
import loci.common.Region;
import loci.common.services.ServiceException;
import loci.formats.CoreMetadata;
import loci.formats.FormatException;
import loci.formats.FormatReader;
import loci.formats.FormatTools;
import loci.formats.MetadataTools;
import loci.formats.SubResolutionFormatReader;
import loci.formats.codec.JPEGTileDecoder;
import loci.formats.meta.MetadataStore;
import loci.formats.services.JPEGTurboService;
import loci.formats.services.JPEGTurboServiceImpl;
import ome.xml.meta.OMEXMLMetadata;

import ome.xml.model.primitives.PositiveFloat;
import ome.xml.model.primitives.PositiveInteger;
import ome.units.quantity.Length;

class OlympusINICoreMetadata extends CoreMetadata {
  int iniIndex;
  OlympusINICoreMetadata() {
    super();
  }
}


/**
 * Olympus SlideScan.ini is the file format reader for Olympus ini datasets.
 *
 * @author Paul Richards paulrichards321@gmail.com
 */
public class OlympusINIReader extends SubResolutionFormatReader { // FormatReader { 
  // -- Constants --

  private static String iniNames[][] = { 
    { "FinalScan.ini", "Finalscan.ini",
      "finalScan.ini", "finalscan.ini" },
    { "FinalCond.ini", "Finalcond.ini",
      "finalCond.ini", "finalcond.ini" },
    { "SlideScan.ini", "Slidescan.ini",
      "slideScan.ini", "slidescan.ini" },
    { "SlideCond.ini", "Slidecond.ini",
      "slideCond.ini", "slidecond.ini" }
  };
  private ArrayList<String> iniPaths = new ArrayList<String>();
  private static String iImageWidth = "iImageWidth";
  private static String iImageHeight = "iImageHeight";
  private static String lXStageRef = "lXStageRef";
  private static String lYStageRef = "lYStageRef";
  private static String lYStepSize = "lYStepSize";
  private static String lXStepSize = "lXStepSize";
  private static String lXOffset = "lXOffset";
  private static String lYOffset = "lYOffset";
  private static String dMagnification = "dMagnification";
  private static boolean multiRes = false;
  class JpegFileXY {
    public long x, y;
    public long xPixel, yPixel;
    public String fileName;
  }
    
  class IniConf {
    private String name = new String();
    private boolean found = false;
    private long xMin = 0;
    private long xMax = 0;
    private long yMin = 0;
    private long yMax = 0; 
    private long xDiffMin = 0;
    private long yDiffMin = 0;
    private long xStepSize = 0;
    private long yStepSize = 0;
    private long pixelWidth = 0;
    private long pixelHeight = 0;
    private double xAdj = 0.0;
    private double yAdj = 0.0;
    private int totalTiles = 0;
    private long xAxis = 0;
    private long yAxis = 0;
    private long xOffset = 0;
    private long yOffset = 0;
    private long totalWidth = 0;
    private long totalHeight = 0;
    private boolean isPreviewSlide = false;
    private boolean xKnowStepSize = false;
    private boolean yKnowStepSize = false;
    private boolean knowStepSizes = false;
    private ArrayList<JpegFileXY> xyArr = new ArrayList<JpegFileXY>();
  }      
  public int atoi(String s) {
    int value = 0;
    try {
      if (s != null) {
        value = Integer.parseInt(s);
      }
    } catch (NumberFormatException ignore) { }
    return value;
  }
  public long atol(String s) {
    long value = 0;
    try {
      if (s != null) {
        value = Long.parseLong(s);
      }
    } catch (NumberFormatException ignore) { }
    return value;
  }

  private ArrayList<IniConf> iniConf = new ArrayList<IniConf>();
  private double xStart = 0.0;
  private double yStart = 0.0;  
  private int level = 0;
  private long baseWidth = 0;
  private long baseHeight = 0;
  private long xMax = 0;
  private long xMin = 0;
  private long yMax = 0;
  private long yMin = 0;
  private long xAxis = 0;
  private long yAxis = 0;
  private long actualWidth = 0;
  private long actualHeight = 0;
  private double magnification = 40.0d;
  private boolean validObject = false;
  private byte bkgColor = (byte) 0xFF;
// -- Fields --

  private int initializedSeries = -1;
  private int initializedPlane = -1;
  private String initializedFile = null;
  private JPEGTurboService service;

  // -- Constructor --

  /** Constructs a new OlympusINIReader. */
  public OlympusINIReader() {
    super("Olympus SlideScan.ini", "ini");
    setFlattenedResolutions(false);  
    domains = new String[] {FormatTools.HISTOLOGY_DOMAIN};
    datasetDescription = "Four .ini files plus several .jpg files";
  }

  // -- IFormatReader API methods --

  /* @see loci.formats.IFormatReader#getOptimalTileWidth() */
  @Override
  public int getOptimalTileWidth() {
    FormatTools.assertId(currentId, true, 1);
    if (validObject) {
      return (int) iniConf.get(0).pixelWidth;
    } else {
      return 752;
    }
  }

  /* @see loci.formats.IFormatReader#getOptimalTileHeight() */
  @Override
  public int getOptimalTileHeight() {
    FormatTools.assertId(currentId, true, 1);
    if (validObject) {
      return (int) iniConf.get(0).pixelHeight;
    } else {
      return 480;
    }
  }

  public void setBkgColor(byte newColor) {
    bkgColor = newColor;
  }

  /* @see loci.formats.IFormatReader#getSeriesUsedFiles(boolean) */
  @Override
  public String[] getSeriesUsedFiles(boolean noPixels) {
    if (noPixels || currentId == null) {
      return null;
    }
    ArrayList<String> f = new ArrayList<String>();
    f.add(currentId);
    for (int i=0; i<iniPaths.size(); i++) { 
      String path=iniPaths.get(i);
      if (currentId != null && currentId.toLowerCase().contains(iniNames[i][3])==false) {
        f.add(path);
      }
    }
    for (int i=0; i<4; i++) {
      IniConf currIniConf = iniConf.get(i);
      if (currIniConf.found) {
        for (JpegFileXY xyfile : currIniConf.xyArr) {
          f.add(xyfile.fileName);
        }
      }
    }
    return f.toArray(new String[f.size()]);
  }

  /* @see loci.formats.IFormatReader#openThumbBytes(int) */
  @Override
  public byte[] openThumbBytes(int no) throws FormatException, IOException {
    int totalCores = core.size();
    int seriesCount = getSeriesCount();
    if (totalCores <= 1 && seriesCount <= 1) {
      return super.openThumbBytes(no);
    }
    int oldSeries = getSeries();
    if (seriesCount > 0) {
      setSeries(seriesCount-1);
    } 
    totalCores = core.size();
    LOGGER.warn("ZoldSeries "+oldSeries+" seriesCount="+seriesCount+ " coreCount="+totalCores+" no="+no);
    int oldIndex = getCoreIndex();
    setCoreIndex(totalCores-1);
    byte[] data = FormatTools.openThumbBytes(this, no);
    setCoreIndex(oldIndex);
    setSeries(oldSeries);
    return data;
  }

  /**
   * @see loci.formats.IFormatReader#openBytes(int, byte[], int, int, int, int)
   */
  @Override
  public byte[] openBytes(int no, byte[] buf, int x, int y, int width, int height)
    throws FormatException, IOException
  {
    FormatTools.checkPlaneParameters(this, no, buf.length, x, y, width, height);
    if (!validObject) return buf;
    int res = getResolution();
    int level = ((OlympusINICoreMetadata) getCurrentCore()).iniIndex;
    if (level==-1 || level >= iniConf.size() || iniConf.get(level).found==false) {
      return buf;
    }
    IniConf currIniConf = iniConf.get(level);
    int actualWidth=(int) currIniConf.totalWidth;
    int actualHeight=(int) currIniConf.totalHeight;
    if (width <= 0 || height <= 0) {
      LOGGER.warn("width or height out of bounds: width=" + width + " height=" + height);
      return buf;
    } 
    int bmpSize=(int) width*height*3;
    java.util.Arrays.fill(buf, 0, bmpSize, bkgColor);
    if (x>actualWidth || x<0 || y>actualHeight || y<0) {
      return buf;
    }
    int fileWidth=(int) currIniConf.pixelWidth;
    int fileHeight=(int) currIniConf.pixelHeight;
    int widthGrab=0, heightGrab=0;
    int totalTilesRead=0;
    boolean found=false;
    for (int tileNum=0; tileNum < currIniConf.totalTiles; tileNum++) {
      int xFilePos=(int) currIniConf.xyArr.get(tileNum).xPixel;
      int yFilePos=(int) currIniConf.xyArr.get(tileNum).yPixel;
      if (((x<xFilePos && x+width>xFilePos) || (x>=xFilePos && x<xFilePos+fileWidth)) &&
          ((y<yFilePos && y+height>yFilePos) || (y>=yFilePos && y<yFilePos+fileHeight))) {
        JPEGReader jpeg = new JPEGReader();
        int xRead=0;
        int xWrite=xFilePos-x;
        widthGrab=(x+width)-xFilePos;
        if (xWrite<0) {
          xWrite=0;
          xRead=x-xFilePos;
          widthGrab=fileWidth-xRead;
          if (widthGrab>width) {
            widthGrab=width;
          }
        }
        int yRead=0;
        int yWrite=yFilePos-y;
        heightGrab=(y+height)-yFilePos;
        if (yWrite<0) {
          yWrite=0;
          yRead=y-yFilePos;
          heightGrab=fileHeight-yRead;
          if (heightGrab>height) {
            heightGrab=height;
          }
        }
        if (yRead+heightGrab>fileHeight) {
          heightGrab=fileHeight-yRead;
        }
        if (xRead+widthGrab>fileWidth) {
          widthGrab=fileWidth-xRead;
        }
        try {
          jpeg.setId(currIniConf.xyArr.get(tileNum).fileName);
          int jpegWidth=jpeg.getSizeX();
          int jpegHeight=jpeg.getSizeY();
          int jpegChannels=jpeg.getSizeC();
          if (heightGrab+yRead>jpegHeight) {
            heightGrab=jpegHeight-yRead;
            if (heightGrab < 0) heightGrab=0;
          }
          if (widthGrab+xRead>jpegWidth) {
            widthGrab=jpegWidth-xRead;
            if (widthGrab < 0) widthGrab=0;
          }
          int tempBmpSize=widthGrab*heightGrab*jpegChannels;
          if (tempBmpSize<=0) {
            tempBmpSize=1;
          }
          byte buf2[] = new byte[tempBmpSize];
          java.util.Arrays.fill(buf2, 0, tempBmpSize, bkgColor);
          jpeg.openBytes(0, buf2, xRead, yRead, widthGrab, heightGrab);
          jpeg.close();
          if (jpegChannels==3) {
            int scansize=(int) widthGrab*heightGrab;
            for (int row=0; row<heightGrab; row++) {
              int desti=(yWrite*width*3)+(xWrite*3)+(row*width*3);
              int srci=widthGrab*row;
              if (desti+(3*widthGrab) > bmpSize || srci+widthGrab+(scansize*2) > buf2.length) {
                LOGGER.warn("In OlympusINIReader::openBytes, pointer out of bounds: bmpSize=" + bmpSize + " desti=" + desti + " tempBmpSize=" + tempBmpSize + " srci=" + srci);
              } else {
                for (int i=0; i<widthGrab; i++) { // BGR RGB
                  buf[desti+2]=buf2[srci];
                  buf[desti+1]=buf2[srci+(scansize)];
                  buf[desti]=buf2[srci+(scansize*2)];
                  desti+=3;
                  srci++;
                }
              }
            }
          } else if (jpegChannels==1) {
            for (int row=yRead; row<heightGrab; row++) {
              int desti=(yWrite*width*3)+(xWrite*3)+(row*width*3);
              int srci=widthGrab*row;
              if (desti+(3*widthGrab) > bmpSize || srci+widthGrab > buf2.length) {
                LOGGER.warn("In OlympusINIReader::openBytes, pointer out of bounds: bmpSize=" + bmpSize + " desti=" + desti + " tempBmpSize=" + tempBmpSize + " srci=" + srci);
              } else {
                for (long i=0; i<widthGrab; i++) { // BGR RGB
                  buf[desti]=buf2[srci];
                  buf[desti+1]=buf2[srci];
                  buf[desti+2]=buf2[srci];
                  desti+=3;
                  srci++;
                }
              }
            }
          } 
        }
        catch (IOException e)
        {
          LOGGER.warn("Warning: failed to read " + currIniConf.xyArr.get(tileNum).fileName + ": " + e.getMessage());
          try {
            jpeg.close();
          } catch (IOException error) { }
        }
        found = true;
      }
    }
    return buf;
  }

  /* @see loci.formats.IFormatReader#close(boolean) */
  @Override
  public void close(boolean fileOnly) throws IOException {
    super.close(fileOnly);
    validObject = false;
    iniConf.clear();
  }

  // -- Internal FormatReader API methods --

  /* @see loci.formats.FormatReader#initFile(String) */
  @Override
  protected void initFile(String id) throws FormatException, IOException {
    Location loc = new Location(id);
    String inputDir = id;
    if (loc != null && loc.isFile()) {
      String parentDir = loc.getParent();
      if (parentDir != null) {
        inputDir = parentDir;
      }
    }
    if (inputDir != null && inputDir.length()>0) {
      char lastKey=inputDir.charAt(inputDir.length()-1);
      if (lastKey=='\\' || lastKey=='/') {
        inputDir=inputDir.substring(0, inputDir.length()-1);
      }
    }
    super.initFile(id);
    boolean yStepSizeFound = false;
    boolean xStepSizeFound = false;
    long xOffset = 0;
    long yOffset = 0;
    int optDebug = 2;

    validObject = false;
    iniConf.clear();
    iniPaths.clear();
    
    for (int i=0; i<4; i++) {
      IniConf iniConfLocal = new IniConf();
      iniConf.add(iniConfLocal);
      iniPaths.add("");
    }
    for (int fileNum = 0; fileNum < 4; fileNum++) {
      IniConf currIniConf = iniConf.get(fileNum);
      String inputName = inputDir;
      inputName += File.separator;
      String inputName2 = inputName;

      boolean foundFile = false;
      for (int s = 0; s < 4 && foundFile == false; s++) {
        inputName2 = inputName;
        inputName2 += iniNames[fileNum][s];
      
        try {
          in = new RandomAccessInputStream(inputName2);
          LOGGER.debug("Found: '" + inputName2 + "'");
          foundFile = true;
        } 
        catch (java.io.IOException ex) {
        }
      }
      if (foundFile == false) {
        LOGGER.warn("Warning: Failed to open: '" + iniNames[fileNum][0] + "'!");
        continue;
      }
      inputName = inputName2;
      currIniConf.name = inputName;

      IniParser parser = new IniParser();
      IniList layout = parser.parseINI(new BufferedReader(
        new InputStreamReader(in, Constants.ENCODING)));
      
      //*****************************************************
      // Parse Start of Header
      //*****************************************************
      IniTable slideHdr = layout.getTable("Header");
      if (slideHdr != null) {
        String width = slideHdr.get(iImageWidth);
        if (width != null && width.length() > 0) {
          currIniConf.pixelWidth=atol(width);
        }
        String height = slideHdr.get(iImageHeight);
        if (height != null && height.length() > 0) {
          currIniConf.pixelHeight=atol(height);
        }
        String xStageSubStr = slideHdr.get(lXStageRef);
        if (xStageSubStr != null && xStageSubStr.length() > 0) {
          currIniConf.xAxis=atol(xStageSubStr);
          xAxis=currIniConf.xAxis;
          LOGGER.debug(" fileNum=" + fileNum + " xAxis="+currIniConf.xAxis);
        }
        String yStageSubStr = slideHdr.get(lYStageRef);
        if (yStageSubStr != null && yStageSubStr.length() > 0) {
          currIniConf.yAxis=atol(yStageSubStr);
          yAxis=currIniConf.yAxis;
          LOGGER.debug(" fileNum=" + fileNum + " yAxis="+currIniConf.yAxis);
        }
        String yStepSubStr = slideHdr.get(lYStepSize);
        if (yStepSubStr != null && yStepSubStr.length() > 0) {
          currIniConf.yStepSize = atol(yStepSubStr);
          if (fileNum==0 && currIniConf.yStepSize > 0) yStepSizeFound = true;
          LOGGER.debug(" fileNum=" + fileNum + " yStepSize=" + currIniConf.yStepSize);
        }
        String xStepSubStr = slideHdr.get(lXStepSize);
        if (xStepSubStr != null && xStepSubStr.length() > 0) {
          currIniConf.xStepSize = atol(xStepSubStr);
          if (fileNum==0 && currIniConf.xStepSize > 0) xStepSizeFound = true;
          LOGGER.debug(" fileNum=" + fileNum + " xStepSize=" + currIniConf.xStepSize);
        }
        String xOffsetSubStr = slideHdr.get(lXOffset);
        if (xOffsetSubStr != null && xOffsetSubStr.length() > 0) {
          xOffset = atol(xOffsetSubStr);
          LOGGER.debug(" xOffset=" + xOffset);
        }
        String yOffsetSubStr = slideHdr.get(lYOffset);
        if (yOffsetSubStr != null && yOffsetSubStr.length() > 0) {
          yOffset = atol(yOffsetSubStr);
          LOGGER.debug(" yOffset=" + yOffset);
        }
        String otherAxis = slideHdr.get("x");
        if (otherAxis != null && otherAxis.length()>0) {
          currIniConf.xAxis = atol(otherAxis);
          LOGGER.debug(" fileNum=" + fileNum + " xAxis="+currIniConf.xAxis);
        }
        otherAxis = slideHdr.get("y");
        if (otherAxis != null && otherAxis.length()>0) {
          currIniConf.yAxis = atol(otherAxis);
          LOGGER.debug(" fileNum=" + fileNum + " yAxis="+currIniConf.yAxis);
        }
        String magSubStr = slideHdr.get(dMagnification);
        if (magSubStr != null && magSubStr.length() > 0) {
          try 
          {
            magnification = Double.parseDouble(magSubStr);
          } catch (NumberFormatException ignore) { }
          LOGGER.debug(" Magnification=" + magnification);
        }
      } else {
        LOGGER.debug("failed to find header in file. ");
        return;
      }
      
      //***************************************************
      // Grab Individual header x y coordinates from file
      //***************************************************
      List<String> headers = layout.getHeaders();
      for (String chunk : headers) {
        if (chunk.equalsIgnoreCase("Header") || chunk.length()==0) continue;
        JpegFileXY jpegxy = new JpegFileXY();
        jpegxy.fileName=inputDir;
        jpegxy.fileName += File.separator;
        jpegxy.fileName += chunk;
        jpegxy.fileName += ".jpg";
        boolean xFound = false;
        boolean yFound = false;
        slideHdr = layout.getTable(chunk);
        if (slideHdr != null) {
          String someNum = slideHdr.get("x");
          if (someNum != null && someNum.length()>0) {
            jpegxy.x = atol(someNum);
            xFound = true;
          }
          someNum = slideHdr.get("y");
          if (someNum != null && someNum.length()>0) {
            jpegxy.y = atol(someNum);
            yFound = true;
          }
        }
        if (xFound && yFound) {
          currIniConf.xyArr.add(jpegxy);
        }
      }
      if (currIniConf.xyArr.size()>0) {
        iniPaths.set(fileNum, inputName);
      }
    }
    
    yMin=0; yMax=0; xMin=0; xMax=0;
    boolean yMinSet=false, xMaxSet=false, xMinSet=false, yMaxSet=false;
    int totalLevels=0;
    for (int fileNum=0; fileNum < 4; fileNum++) {
      IniConf currIniConf=iniConf.get(fileNum);
      if (currIniConf.xyArr.size()==0) continue;
      totalLevels++;

      currIniConf.totalTiles = currIniConf.xyArr.size();
      if (currIniConf.pixelWidth<=0 || currIniConf.pixelHeight<=0) {
        JPEGReader reader = new JPEGReader();
        try {
          reader.setId(currIniConf.xyArr.get(0).fileName);
          currIniConf.pixelWidth=reader.getSizeX();
          currIniConf.pixelHeight=reader.getSizeY();
        } catch (IOException e) {
          LOGGER.error("Parsing jpeg failed on filename="+currIniConf.xyArr.get(0).fileName+" reason: "+e.getMessage());
          return;
        }
        finally {
          try { reader.close(); } catch (IOException e) { }
        }
      }
    
      JPEGReader reader = new JPEGReader();
      try {
        reader.setId(currIniConf.xyArr.get(0).fileName);
        currIniConf.pixelWidth=reader.getSizeX();
        currIniConf.pixelHeight=reader.getSizeY();
      } catch (IOException e) {
        LOGGER.error("Parsing jpeg failed on filename="+currIniConf.xyArr.get(0).fileName+" reason: "+e.getMessage());
        return;
      }
      finally {
        try { reader.close(); } catch (IOException e) { }
      }

      LOGGER.debug("fileName=" + currIniConf.name + " jpegWidth=" + currIniConf.pixelWidth + " jpegHeight=" + currIniConf.pixelHeight);
      currIniConf.found = true;
      
      //************************************************************************
      // Get the xmin and xmax values
      //************************************************************************
      Collections.sort(currIniConf.xyArr, new Comparator<JpegFileXY>() {
        @Override
        public int compare(JpegFileXY coord1, JpegFileXY coord2) {
          long result = coord1.x - coord2.x;
          if (result==0) result = coord1.y - coord2.y;
          return (int) result;
        }
      });
 
      currIniConf.xMin = currIniConf.xyArr.get(0).x;
      currIniConf.xMax = currIniConf.xyArr.get(currIniConf.totalTiles-1).x;
      for (int i=0; i+1 < currIniConf.totalTiles; i++) {
        if (currIniConf.xyArr.get(i+1).x==currIniConf.xyArr.get(i).x) {
          long diff=currIniConf.xyArr.get(i+1).y - currIniConf.xyArr.get(i).y;
          if ((diff>0 && diff<currIniConf.yDiffMin) || (diff>0 && currIniConf.yDiffMin<1)) {
            currIniConf.yDiffMin=diff;
          }
        }
      }

      //************************************************************************
      // Get the ymin and ymax values
      //************************************************************************
      Collections.sort(currIniConf.xyArr, new Comparator<JpegFileXY>() {
        @Override
        public int compare(JpegFileXY coord1, JpegFileXY coord2) {
          long result = coord1.y - coord2.y;
          if (result==0) result = coord1.x - coord2.x;
          return (int) result;
        }
      });
      currIniConf.yMin=currIniConf.xyArr.get(0).y - currIniConf.yDiffMin;
      currIniConf.yMax=currIniConf.xyArr.get(currIniConf.totalTiles-1).y; // + currIniConf.yDiffMin;

      LOGGER.debug("fileName=" + currIniConf.name + " yDiffMin=" + currIniConf.yDiffMin + " yMin=" + currIniConf.yMin + " yMax=" + currIniConf.yMax + " yAxis=" + currIniConf.yAxis);
      for (int i=0; i+1 < currIniConf.totalTiles; i++) {
        LOGGER.debug(" Sorted: x=" + currIniConf.xyArr.get(i).x + " y=" + currIniConf.xyArr.get(i).y);
        if (currIniConf.xyArr.get(i+1).y==currIniConf.xyArr.get(i).y) {
          int diff=(int) (currIniConf.xyArr.get(i+1).x - currIniConf.xyArr.get(i).x);
          if ((diff>0 && diff<currIniConf.xDiffMin) || (diff>0 && currIniConf.xDiffMin<1)) {
            currIniConf.xDiffMin=diff;
          }
        }
      }
      if (currIniConf.xStepSize>0) {
        LOGGER.debug("fileName=" + currIniConf.name + " xAdj calculation exact=");
        currIniConf.xKnowStepSize = true;
      } else {
        if (fileNum>0 && iniConf.get(fileNum-1).found && iniConf.get(fileNum-1).xStepSize>0) {
          currIniConf.xStepSize = iniConf.get(fileNum-1).xStepSize*4;
          currIniConf.xKnowStepSize = true;
        } else {
          if (currIniConf.xDiffMin > 0) {
            currIniConf.xStepSize = currIniConf.xDiffMin;
            currIniConf.xKnowStepSize = true;
          } else {
            currIniConf.xStepSize = Math.abs(currIniConf.xMax);
            currIniConf.xKnowStepSize = false;
          }
        }
        LOGGER.debug("fileName=" + currIniConf.name + " Guessing xAdj=");
      }
      if (currIniConf.pixelWidth>0 && currIniConf.xStepSize>0) {
        currIniConf.xAdj = (double) currIniConf.xStepSize / (double) currIniConf.pixelWidth;
        LOGGER.debug(Double.toString(currIniConf.xAdj));
      }
     
      if (currIniConf.yStepSize>0) {
        LOGGER.debug("fileName=" + currIniConf.name + " yAdj calculation exact=");
        currIniConf.yKnowStepSize = true;
      } else {
        if (fileNum>0 && iniConf.get(fileNum-1).found && iniConf.get(fileNum-1).yStepSize>0) {
          currIniConf.yStepSize = (long) (iniConf.get(fileNum-1).yStepSize*4);
          currIniConf.yKnowStepSize = true;
        } else {
          if (currIniConf.yDiffMin > 0) {
            currIniConf.yStepSize = currIniConf.yDiffMin;
            currIniConf.yKnowStepSize = true;
          } else {
            currIniConf.yStepSize = Math.abs(currIniConf.yMax);
            currIniConf.yKnowStepSize = false;
          }
        }
        LOGGER.debug("fileName=" + currIniConf.name + " Guessing yAdj=");
      }
      currIniConf.knowStepSizes = (currIniConf.xKnowStepSize && currIniConf.yKnowStepSize) ? true : false;
      if (currIniConf.pixelHeight>0 && currIniConf.yStepSize>0) {
        currIniConf.yAdj = (double) currIniConf.yStepSize / (double) currIniConf.pixelHeight;
        LOGGER.debug(Double.toString(currIniConf.yAdj));
      }
   
      LOGGER.debug("fileName=" + currIniConf.name + " xDiffMin=" + currIniConf.xDiffMin + " xMin=" + currIniConf.xMin + " xMax=" + currIniConf.xMax);
      if (currIniConf.pixelWidth>0) {
        if (currIniConf.xStepSize>0) {
          currIniConf.xAdj = (double) currIniConf.xStepSize / (double) currIniConf.pixelWidth;
        } else if (fileNum>0) {
          currIniConf.xAdj = (double) (iniConf.get(fileNum-1).xStepSize*4) / (double) currIniConf.pixelWidth;
        }
        LOGGER.debug("fileName=" + currIniConf.name + " Guessed xAdj=" + currIniConf.xAdj);
      }
      if (currIniConf.pixelHeight>0) {
        if (currIniConf.yStepSize>0) {
          currIniConf.yAdj = (double) currIniConf.yStepSize / (double) currIniConf.pixelHeight;
        } else {
          currIniConf.yAdj = (double) (iniConf.get(fileNum-1).yStepSize*4) / (double) currIniConf.pixelHeight;
        }
        LOGGER.debug("fileName=" + currIniConf.name + " Guessed yAdj=" + currIniConf.yAdj);
      }
      if ((yMinSet==false || currIniConf.yMin < yMin) && fileNum < 3) {
        yMin=currIniConf.yMin;
        yMinSet = true;
      }
      if ((yMaxSet==false || currIniConf.yMax > yMax) && fileNum < 3) {
        yMax=currIniConf.yMax;
        yMaxSet = true;
      }
      if ((xMinSet==false || currIniConf.xMin < xMin) && fileNum < 3) { 
        xMin=currIniConf.xMin;
        xMinSet = true;
      }
      if ((xMaxSet==false || currIniConf.xMax > xMax) && fileNum < 3) {
        xMax=currIniConf.xMax;
        xMaxSet = true;
      }
    }
    

    boolean iniSortByAdj=true;
    for (int i=0; i<4; i++) {
      if (iniConf.get(i).found==false || iniConf.get(i).xAdj==0 || iniConf.get(i).yAdj==0) {
        iniSortByAdj=false;
      }
    }
    if (iniSortByAdj) {
      Collections.sort(iniConf, new Comparator<IniConf>() {
        @Override
        public int compare(IniConf conf1, IniConf conf2) {
          long result = (long)(conf1.totalWidth * conf1.totalHeight) - (long)(conf2.totalWidth * conf2.totalHeight);
          if (result > 0) return -1;
          else if (result < 0) return 1;
          else return 0;
        }
      });
    }
    for (int fileNum=0; fileNum < 4; fileNum++) {
      if (iniConf.get(fileNum).xAxis==0 || iniConf.get(fileNum).yAxis==0) {
        int targetFileNum;
        if (fileNum==0 && iniConf.get(2).xAxis > 0) {
          targetFileNum = 2;
        } else if (fileNum==0 && iniConf.get(1).xAxis > 0) {
          targetFileNum = 1;
        } else if (fileNum==2 && iniConf.get(0).xAxis > 0) {
          targetFileNum = 0;
        } else if (fileNum==2 && iniConf.get(1).xAxis > 0) {
          targetFileNum = 1;
        } else if (fileNum==1 || fileNum==3) {
          targetFileNum = fileNum - 1;
        } else {
          targetFileNum = -1;
        }
        if (targetFileNum >= 0) {
          iniConf.get(fileNum).xAxis = iniConf.get(targetFileNum).xAxis;
          iniConf.get(fileNum).yAxis = iniConf.get(targetFileNum).yAxis;
        } else {
          iniConf.get(fileNum).xAxis=278000;
          iniConf.get(fileNum).yAxis=142500;
        }
      }
    }
 
    IniConf higherConf = null;
    IniConf lowerConf = null;
    int higherLevel = -1;
    int lowerLevel = -1;
    boolean higherLevelFound = false, lowerLevelFound = false;
    IniConf confZero = iniConf.get(0);
    IniConf confOne = iniConf.get(1);
    IniConf confTwo = iniConf.get(2);
    IniConf confThree = iniConf.get(3);
    if (confTwo.found && confTwo.knowStepSizes) {
      higherConf = confTwo;
      higherLevelFound = true;
      higherLevel = 2;
    } else if (confThree.found && confThree.knowStepSizes) {
      higherConf = confThree;
      higherLevelFound = true;
      higherLevel = 3;
    }
    if (confZero.found) {
      lowerConf = confZero;
      lowerLevel = 0;
      lowerLevelFound = true;
    }
    if (confOne.found) {
      lowerConf = confOne;
      lowerLevel = 1;
      lowerLevelFound = true;
    }
  
    //****************************************************************
    // Guess the total image width and height for each pyramid level
    //****************************************************************
    double multiX[] = { 1.0, 1.0, 1.0 };
    double multiY[] = { 1.0, 1.0, 1.0 };
    
    if (confThree.found && confTwo.found) {
      multiX[2] = confTwo.xAdj / confThree.xAdj;
      multiY[2] = confTwo.yAdj / confThree.yAdj;
    }
    if (confTwo.found && confOne.found) {
      multiX[1] = confTwo.xAdj / confOne.xAdj;
      multiY[1] = confTwo.yAdj / confOne.yAdj;
    }
    else if (confThree.found && confOne.found) {
      multiX[1] = confThree.xAdj / confOne.xAdj;
      multiY[1] = confThree.yAdj / confOne.yAdj;
    }
    if (confZero.found) {
      if (confTwo.found) {
        multiX[0] = confTwo.xAdj / confZero.xAdj;
        multiY[0] = confTwo.yAdj / confZero.yAdj;
      }
      else if (confThree.found) {
        multiX[0] = confThree.xAdj / confZero.xAdj;
        multiY[0] = confThree.yAdj / confZero.yAdj;
      }
      else if (confOne.found) {
        multiX[0] = confOne.xAdj / confZero.xAdj;
        multiY[0] = confOne.yAdj / confZero.yAdj;
      }
    }
    
    if (confTwo.found && confTwo.knowStepSizes) {
      confTwo.totalWidth = (long)Math.floor((double)(confTwo.xMax - (confTwo.xMin - confTwo.xStepSize)) / (double) confTwo.xAdj);
      confTwo.totalHeight = (long)Math.floor((double)(confTwo.yMax - (confTwo.yMin - confTwo.yStepSize)) / (double) confTwo.yAdj);

      confThree.totalWidth = (long) Math.floor(confTwo.totalWidth * multiX[2]);
      confThree.totalHeight = (long) Math.floor(confTwo.totalHeight * multiY[2]);

      confOne.totalWidth = (long) Math.floor(confTwo.totalWidth * multiX[1]);
      confOne.totalHeight = (long) Math.floor(confTwo.totalHeight * multiY[1]);

      confZero.totalWidth = (long) Math.floor(confTwo.totalWidth * multiX[0]);
      confZero.totalHeight = (long) Math.floor(confTwo.totalHeight * multiY[0]);
      LOGGER.debug("All conf level width and height known.");
    } else if (confThree.found && confThree.knowStepSizes) {
      confThree.totalWidth = (long) Math.floor((double)(confThree.xMax - (confThree.xMin - confThree.xStepSize)) / (double) confThree.xAdj);
      confThree.totalHeight = (long) Math.floor((double)(confThree.yMax - (confThree.yMin - confThree.yStepSize)) / (double) confThree.yAdj);

      confOne.totalWidth = (long) Math.floor(confThree.totalWidth * multiX[1]);
      confOne.totalHeight = (long) Math.floor(confThree.totalHeight * multiY[1]);
      confZero.totalWidth = (long) Math.floor(confThree.totalWidth * multiX[0]);
      confZero.totalHeight = (long) Math.floor(confThree.totalHeight * multiY[0]);
      LOGGER.debug("0,1,2 conf level width and height known.");
    } else if (confOne.found && confOne.knowStepSizes) {
      confOne.totalWidth = (long) Math.floor((double)(confOne.xMax - (confOne.xMin - confOne.xStepSize)) / (double) confOne.xAdj);
      confOne.totalHeight = (long) Math.floor((double)(confOne.yMax - (confOne.yMin - confOne.yStepSize)) / (double) confOne.yAdj);

      confZero.totalWidth = (long) Math.floor(confOne.totalWidth * multiX[0]);
      confZero.totalHeight = (long) Math.floor(confOne.totalHeight * multiY[0]);
      LOGGER.debug("0,1 conf level width and height known.");
    } else {
      for (int fileNum=0; fileNum < 4; fileNum++) {
        IniConf currIniConf = iniConf.get(fileNum);
        currIniConf.totalWidth = (long) Math.floor((double)(currIniConf.xMax - (currIniConf.xMin - currIniConf.xStepSize)) / (double) currIniConf.xAdj);
        currIniConf.totalHeight = (long) Math.floor((double)(currIniConf.yMax - (currIniConf.yMin - currIniConf.yStepSize)) / (double) currIniConf.yAdj);
      }
      LOGGER.debug("All conf level width and height known.");
    }

    // log file width and height
    for (int fileNum=0; fileNum < 4; fileNum++) {
      LOGGER.debug("fileName=" + iniConf.get(fileNum).name + " totalWidth in pixels=" + iniConf.get(fileNum).totalWidth + " totalHeight in pixels=" + iniConf.get(fileNum).totalHeight);
    }

    //*******************************************************************
    // Find the pyramid level lowest zoom and set that as current image
    //*******************************************************************
    level=-1;
    for (int min=3; min>=0; min--) {
      if (iniConf.get(min).found==true) {
        level=min;
        break;
      }
    }
    if (level==-1) {
      LOGGER.warn("File has no readable levels.");
      validObject = false;
      return;
    }
    validObject = true;

    long bestXOffsetL0=0, bestXOffsetL1=0;
    long bestYOffsetL0=0, bestYOffsetL1=0;
    if (lowerLevelFound && higherLevelFound) {
      double higherRatioX = (double) higherConf.pixelWidth / (double) higherConf.xStepSize; 
      double higherRatioY = (double) higherConf.pixelHeight / (double) higherConf.yStepSize;

      double higherMinBaseX = (double) (lowerConf.xAxis - higherConf.xMax);
      double higherMinBaseY = (double) (lowerConf.yAxis - higherConf.yMax);

      if (confZero.found) {
        double ratioAL0X = (double) confZero.pixelWidth / (double) confZero.xStepSize;
        double ratioAL0Y = (double) confZero.pixelHeight / (double) confZero.yStepSize;
        double ratioBL0X = (double) higherConf.xStepSize / (double) confZero.xStepSize;
        double ratioBL0Y = (double) higherConf.yStepSize / (double) confZero.yStepSize;

        double stageBaseL0X = (double) confZero.xAxis + ((double) higherConf.xStepSize / 2);
        stageBaseL0X -= (double) confZero.xStepSize / 2;

        double stageBaseL0Y = (double) confZero.yAxis + ((double) higherConf.yStepSize / 2);
        stageBaseL0Y -= (double) confZero.yStepSize / 2;

        double lowerMinBaseL0X = stageBaseL0X - confZero.xMax;
        double lowerMinBaseL0Y = stageBaseL0Y - confZero.yMax;
     
        double minusL0X = higherMinBaseX * higherRatioX * ratioBL0X;
        double minusL0Y = higherMinBaseY * higherRatioY * ratioBL0Y;

        bestXOffsetL0 = (long) Math.ceil(lowerMinBaseL0X * ratioAL0X - minusL0X);
        bestYOffsetL0 = (long) Math.ceil(lowerMinBaseL0Y * ratioAL0Y - minusL0Y);
      }
      if (confOne.found) {
        double ratioAL1X = (double) confOne.pixelWidth / (double) confOne.xStepSize;
        double ratioAL1Y = (double) confOne.pixelHeight / (double) confOne.yStepSize;
        double ratioBL1X = (double) higherConf.xStepSize / (double) confOne.xStepSize;
        double ratioBL1Y = (double) higherConf.yStepSize / (double) confOne.yStepSize;

        double stageBaseL1X = (double) confOne.xAxis + ((double) higherConf.xStepSize / 2);
        stageBaseL1X -= (double) confOne.xStepSize / 8;

        double stageBaseL1Y = (double) confOne.yAxis + ((double) higherConf.yStepSize / 2);
        stageBaseL1Y -= (double) confOne.yStepSize / 8;

        double lowerMinBaseL1X = stageBaseL1X - confOne.xMax;
        double lowerMinBaseL1Y = stageBaseL1Y - confOne.yMax;
     
        double minusL1X = higherMinBaseX * higherRatioX * ratioBL1X;
        double minusL1Y = higherMinBaseY * higherRatioY * ratioBL1Y;

        bestXOffsetL1 = (long) Math.ceil(lowerMinBaseL1X * ratioAL1X - minusL1X);
        bestYOffsetL1 = (long) Math.ceil(lowerMinBaseL1Y * ratioAL1Y - minusL1Y);
      }
    }
    LOGGER.debug("Best X Offset Level0=" + bestXOffsetL0);
    LOGGER.debug("Best Y Offset Level0=" + bestYOffsetL0);
    LOGGER.debug("Best X Offset Level1=" + bestXOffsetL1);
    LOGGER.debug("Best Y Offset Level1=" + bestYOffsetL1);
   
    //*****************************************************************
    // Calculate the x and y coordinate of each file starting pixels
    //*****************************************************************
    for (int fileNum=0; fileNum<4; fileNum++) {
      IniConf currIniConf=iniConf.get(fileNum);
      if (currIniConf.found==false) continue;
      
      for (int i=0; i<currIniConf.totalTiles; i++) {
        double xPixel;
        xPixel=(double)(currIniConf.xMax - currIniConf.xyArr.get(i).x)/(double)currIniConf.xAdj;
        double yPixel;
        yPixel=(double)(currIniConf.yMax - currIniConf.xyArr.get(i).y)/(double)currIniConf.yAdj;
 
        if (higherLevelFound && fileNum==0) {
          xPixel += bestXOffsetL0;
          yPixel += bestYOffsetL0;
        } else if (higherLevelFound && fileNum==1) {
          xPixel += bestXOffsetL1;
          yPixel += bestYOffsetL1;
        }
        currIniConf.xyArr.get(i).xPixel=(long)xPixel;
        currIniConf.xyArr.get(i).yPixel=(long)yPixel;

        LOGGER.debug("filename=" + currIniConf.xyArr.get(i).fileName + " x=" + xPixel + " y=" + yPixel);
      }
      Collections.sort(currIniConf.xyArr, new Comparator<JpegFileXY>() {
        @Override
        public int compare(JpegFileXY coord1, JpegFileXY coord2) {
          long result = coord1.yPixel - coord2.yPixel;
          if (result == 0) result = coord1.xPixel - coord2.xPixel;
          return (int) result;
        }
      });
    }

    baseWidth = iniConf.get(0).totalWidth;
    baseHeight = iniConf.get(0).totalHeight;

    // Trim the last level
    if (totalLevels >= 4) {
      totalLevels = 3;
    }
    core.clear();
    int seriesCount = totalLevels;
    int resCount = 0;
    
    setSeries(0);

    multiRes = false;
    if (iniConf.get(0).found &&   
        iniConf.get(1).found) {
      multiRes = true;
      resCount = 2;
    }

    if (multiRes) {
      core.add();
      core.add(0, new OlympusINICoreMetadata());
      core.add(0, new OlympusINICoreMetadata());
      
      if (iniConf.get(2).found) {
        core.add();
        core.add(1, new OlympusINICoreMetadata());
      }
    } else {
      for (int s = 0; s < totalLevels; s++) {
        core.add(new OlympusINICoreMetadata());
      }
    }
    for (int s = 0; s < seriesCount; s++) {
      int coreIndex = 0;
      int res = 0;
      int i = s;
      OlympusINICoreMetadata ms = null;
      if (multiRes) {
        if (s < resCount) {
          res = s;
        } else {
          coreIndex = (i - resCount) + 1;
        }
      } else {
        coreIndex = s;
      }
      if (iniConf.get(i).found) {
        ms = (OlympusINICoreMetadata) core.get(coreIndex, res);
        setCoreIndex(s);

        if (multiRes == true) {
          if (s == 0) {
            ms.resolutionCount = resCount;
          } else if (res == 0) {
            ms.resolutionCount = 1;
          }
        }
        ms.sizeX = (int) iniConf.get(i).totalWidth;
        ms.sizeY = (int) iniConf.get(i).totalHeight;
        ms.sizeZ = 1;
        ms.sizeT = 1;
        ms.sizeC = 3;
        ms.rgb = true;
        ms.imageCount = 1;
        ms.dimensionOrder = "XYCZT";
        ms.pixelType = FormatTools.UINT8;
        ms.interleaved = true;
        ms.falseColor = false;
        ms.bitsPerPixel = 8;
        ms.thumbnail = (multiRes && s == 0) ? false : true;
        ms.metadataComplete = true;
        ms.littleEndian = false;
        ms.indexed = false;
        ms.iniIndex = i;
      }
    }

    MetadataStore store = makeFilterMetadata();
    MetadataTools.populatePixels(store, this);

    String instrumentID = MetadataTools.createLSID("Instrument", 0);
    String objectiveID = MetadataTools.createLSID("Objective", 0, 0);

    store.setInstrumentID(instrumentID, 0);
    store.setObjectiveID(objectiveID, 0, 0);
    store.setObjectiveNominalMagnification(magnification, 0, 0);

    store.setObjectiveSettingsID(objectiveID, 0);
    LOGGER.info("Olympus INI has multiple resolutions="+multiRes);

    double currMag = magnification;
    int separateCores = 0;
    if (multiRes) {
      if (totalLevels >= 3) {
        separateCores = 2;
      }
      else if (totalLevels > 0) {
        separateCores = 1;
      }
    } else {
      separateCores = totalLevels;
    }
    int totalCores = 0;
    for (int s = 0; s < separateCores; s++) {
      int i = s;
      if (multiRes && s > 0) {
        i++;
      }
      if (iniConf.get(i).found) {
        store.setPixelsSizeX(new PositiveInteger((int) iniConf.get(i).totalWidth), totalCores);
        store.setPixelsSizeY(new PositiveInteger((int) iniConf.get(i).totalHeight), totalCores);
        store.setPixelsSizeC(new PositiveInteger(3), totalCores);
        store.setPixelsSizeT(new PositiveInteger(1), totalCores);
        store.setPixelsSizeZ(new PositiveInteger(1), totalCores);
        
        DecimalFormat df = new DecimalFormat("##.##");
        df.setMaximumFractionDigits(2);
        if (multiRes) {
          if (s == 0) {
            store.setImageName("0 "+df.format(currMag)+"x", totalCores);
          } else {
            store.setImageName("macro image "+df.format(currMag)+"x", totalCores);
          }
        } else {
          store.setImageName(""+totalCores+" "+df.format(currMag)+"x", totalCores);
        }
        store.setImageInstrumentRef(instrumentID, totalCores);
        
        totalCores++;
      }
      if (multiRes) {
        if (s == 0) {
          currMag /= 8;
        } else {
          currMag /= 4;
        }
      } else {
        if (s == 0) {
          currMag /= 2;
        } else {
          currMag /= 4;
        }
      }
    }
 
    if (getMetadataOptions().getMetadataLevel() != MetadataLevel.MINIMUM) {
      String experimenterID = MetadataTools.createLSID("Experimenter", 0);
      store.setExperimenterID(experimenterID, 0);
      
      totalCores = 0;
      for (int s = 0; s < separateCores; s++) {
        int i = s;
        if (multiRes && s > 0) {
          i++;
        }
        if (iniConf.get(i).found) {
          Length sizeX = FormatTools.getPhysicalSizeX((double) iniConf.get(i).xAdj);
          Length sizeY = FormatTools.getPhysicalSizeY((double) iniConf.get(i).yAdj);
          if (sizeX != null) {
            store.setPixelsPhysicalSizeX(sizeX, totalCores);
          }
          if (sizeY != null) {
            store.setPixelsPhysicalSizeY(sizeY, totalCores);
          }
          store.setPixelsPhysicalSizeZ(null, totalCores);
          totalCores++;
        }
      }
    }
    setSeries(0);
    return;
  }
}

