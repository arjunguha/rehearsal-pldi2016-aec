@using $rootnamespace$.Extensions
@using MvcSiteMapProvider.Web.Html

@(Request.IsAuthenticated ? Html.MvcSiteMap("System").Nav(false) : Html.MvcSiteMap("Public").Nav(false))
