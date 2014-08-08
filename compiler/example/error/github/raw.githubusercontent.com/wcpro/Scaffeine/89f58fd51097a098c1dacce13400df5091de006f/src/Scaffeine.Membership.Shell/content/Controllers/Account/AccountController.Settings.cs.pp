namespace $rootnamespace$.Controllers.Account
{
    using System.Web.Mvc;
    using Core.Common.Membership;
    using Extensions;
    using Models;

    public partial class AccountController
    {              
		public ActionResult Settings()
        {
            ViewBag.PasswordLength = System.Web.Security.Membership.MinRequiredPasswordLength;
            return View();
        }

        [HttpPost]
        public ActionResult Settings(ChangePasswordModel model)
        {
            if (ModelState.IsValid)
            {
                var status = _userService.ChangePassword(this.GetCurrentUser(), model.OldPassword, model.NewPassword);

                switch (status)
                {
                    case ChangePasswordStatus.Success:
                        TempData["Success"] = "Password was changed successfully";
                        break;
                    case ChangePasswordStatus.Failure:
                        ModelState.AddModelError(string.Empty, "The current password is incorrect or the new password is invalid.");
                        break;
                }           
            }

            ViewBag.PasswordLength = System.Web.Security.Membership.MinRequiredPasswordLength;
            return View(model);
        }
    }
}
