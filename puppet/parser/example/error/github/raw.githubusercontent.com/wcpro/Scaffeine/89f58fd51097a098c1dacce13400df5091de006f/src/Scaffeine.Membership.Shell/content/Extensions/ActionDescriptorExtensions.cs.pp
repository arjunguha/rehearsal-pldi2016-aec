namespace $rootnamespace$.Extensions
{
    using System.Web.Mvc;
    using System.Web.Routing;
    using System;

    public static class ActionDescriptorExtensions
    {
        public static void SafeRedirect(this ActionExecutingContext context, string actionName, string controllerName)
        {
            var aName = context.ActionDescriptor.ActionName;
            var cName = context.ActionDescriptor.ControllerDescriptor.ControllerName;

            if (!(controllerName.Equals(cName, StringComparison.InvariantCultureIgnoreCase) && actionName.Equals(aName, StringComparison.InvariantCultureIgnoreCase)))
            {
                context.Result = new RedirectToRouteResult(new RouteValueDictionary
                        {
                            { "controller", controllerName },
                            { "action", actionName }                                                 
                        });
            }
        }
    }
}