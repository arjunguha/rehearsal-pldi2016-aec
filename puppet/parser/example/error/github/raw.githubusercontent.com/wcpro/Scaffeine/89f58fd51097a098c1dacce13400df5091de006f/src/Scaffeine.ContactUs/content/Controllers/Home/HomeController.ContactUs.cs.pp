namespace $rootnamespace$.Controllers.Home
{
    using System.Web.Mvc;

    using Mvc.Mailer;

    using Mailers;
    using Models;

    public partial class HomeController
    {
        [AllowAnonymous]
        [HttpGet]
        public ActionResult Contact()
        {
            return View(new ContactUsModel());
        }

        [AllowAnonymous]
        [HttpPost]
        public ActionResult Contact(ContactUsModel model)
        {
            if (ModelState.IsValid)
            {
                new Mailer().ContactUs(model).Send();
            }

            return View(model);
        }
    }
}
