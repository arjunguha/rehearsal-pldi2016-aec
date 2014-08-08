using System.Web.Mvc;

namespace $rootnamespace$.Controllers.Account
{
    public partial class AccountController
    {

        public ActionResult Identity()
        {
            return View(HttpContext.User);
        }


    }
}
