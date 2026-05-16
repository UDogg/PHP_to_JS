<?php

use Illuminate\Database\Migrations\Migration;
use Illuminate\Database\Schema\Blueprint;
use Illuminate\Support\Facades\Schema;

return new class extends Migration
{
    /**
     * Run the migrations.
     */
    public function up()
    {
        if(!Schema::hasTable('sso_api_tokens')){
        Schema::create('sso_api_tokens', function (Blueprint $table) {
            $table->id();
            $table->string('sso_api_token');
            $table->string('formData')->nullable();
            $table->enum('status', ['Y', 'N'])->default('Y');
            $table->timestamps();

         });
        }
    }

    public function down()
    {
        Schema::dropIfExists('sso_api_tokens');
    }
};
