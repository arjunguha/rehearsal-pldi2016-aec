@using $rootnamespace$.Extensions
@using MvcSiteMapProvider.Web.Html
@{
    Layout = "~/Views/Shared/_Layout.cshtml";  
	if (ViewBag.SitemapProvider == null)
    {
        ViewBag.SitemapProvider = "Modules";
    }
}
@RenderSection("Stylesheets", false)
@RenderSection("Scripts", false)
<div class="row-fluid">
    <div class="span2">

        

        @RenderSection("UserActions", false)
        @if (!this.IsSectionDefined("UserActions"))
        {
            <div class="folder-actions">
                @Html.Partial("_UserActions")
            </div>            
        }
        @{
            SiteMapProvider provider = SiteMap.Providers[ViewBag.SitemapProvider];
        }
        @Html.MvcSiteMap(provider).Pills(0, true, true, 1)
    </div>
    <div class="span10" id="mainPanel">        
        @Html.MvcSiteMap((string)ViewBag.SitemapProvider).Breadcrumb()
        <div class="row-fluid">            
            @RenderBody()
        </div>
    </div>
</div>

@section footer{
    <span></span>
}
